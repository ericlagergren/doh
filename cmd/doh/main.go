// Command doh implements a dig-like utility for DNS over HTTPS.
package main

import (
	"bytes"
	"context"
	"crypto/rand"
	"encoding/base64"
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"io/ioutil"
	"log"
	"math/big"
	"net/http"
	"net/url"
	"os"
	"path/filepath"
	"runtime"
	"strconv"
	"strings"
	"sync"
	"time"

	"github.com/miekg/dns"
	"golang.org/x/sync/errgroup"
)

var base = filepath.Base(os.Args[0])

func main() {
	var (
		chatty  bool
		json    bool
		id      uint16
		rd      bool
		do      bool
		get     bool
		timeout time.Duration
	)
	flag.Var((*uint16Flag)(&id), "id", "set the 16-bit identification field")
	flag.BoolVar(&rd, "rd", true, "set the Recursion Desired bit")
	flag.BoolVar(&do, "do", false, "request DNSSEC data")
	flag.BoolVar(&get, "get", false, "perform a GET request instead of POST")
	flag.BoolVar(&json, "json", false, "perform a DoH request with JSON instead of RFC 8484")
	flag.DurationVar(&timeout, "t", 2*time.Second, "HTTPS timeout")
	flag.BoolVar(&chatty, "v", false, "be more verbose")

	flag.Usage = func() {
		fmt.Fprintf(os.Stderr,
			"Usage: %s [OPTIONS] @SERVER NAME [TYPE] [CLASS]\n", base)
		flag.PrintDefaults()
	}
	flag.Parse()

	logger := log.New(os.Stderr, base+": ", 0)
	fatalf := func(format string, args ...interface{}) {
		logger.Fatalf(format, args...)
	}

	var (
		ns   string
		msgs []*dns.Msg
	)
	for _, arg := range flag.Args() {
		if strings.HasPrefix(arg, "@") {
			ns = strings.TrimPrefix(arg, "@")
			continue
		}
		if t, ok := dns.StringToType[up(arg)]; ok {
			if len(msgs) == 0 {
				fatalf("must specify domain name before query type")
			}
			msgs[len(msgs)-1].Question[0].Qtype = t
			continue
		}
		if c, ok := dns.StringToClass[up(arg)]; ok {
			if len(msgs) == 0 {
				fatalf("must specify domain name before class type")
			}
			msgs[len(msgs)-1].Question[0].Qclass = c
			continue
		}
		msg := &dns.Msg{
			MsgHdr: dns.MsgHdr{
				Id:               id,
				Opcode:           dns.OpcodeQuery,
				RecursionDesired: rd,
			},
			Question: []dns.Question{{
				Name:   dns.Fqdn(arg),
				Qtype:  dns.TypeA,
				Qclass: dns.ClassINET,
			}},
		}
		msg.SetEdns0(1220, do) // RFC 2671
		msgs = append(msgs, msg)
	}

	if ns == "" {
		fatalf("must provide a name server")
	}
	if !strings.HasPrefix(ns, "https://") {
		ns = "https://" + ns
	}
	u, err := url.Parse(ns)
	if err != nil {
		fatalf("doh: unable to parse name server URI %q: %v", ns, err)
	}
	if u.Scheme != "https" {
		fatalf("doh: invalid scheme: %q", u.Scheme)
	}
	u.Host = dns.Fqdn(u.Host)

	// Override -json since Google responds with HTTP status 400 if we send a
	// non-JSON request to /resolve.
	if u.Host == "dns.google." {
		json = u.Path == "/resolve"
	}

	ctx := context.Background()
	ctx, cancel := context.WithTimeout(ctx, 2*time.Second)
	defer cancel()

	c := &config{
		client: &http.Client{
			Timeout: 2 * time.Second,
		},
		json:   json,
		get:    get,
		chatty: chatty,
		log:    logger,
	}

	w := &syncWriter{w: os.Stdout}

	sem := make(chan struct{}, runtime.GOMAXPROCS(-1))
	grp, ctx := errgroup.WithContext(ctx)
	for _, m := range msgs {
		m := m
		sem <- struct{}{}
		grp.Go(func() error {
			defer func() { <-sem }()
			q, err := c.query(ctx, u, m)
			if err != nil {
				return err
			}
			io.WriteString(w, q.String())
			return nil
		})
	}

	if err := grp.Wait(); err != nil {
		fatalf("query failure: %v", err)
	}
}

const (
	badMime = iota
	msgMime
	jsonMime
)

func sniffMime(s string) int {
	switch s {
	case msgMimeType:
		return msgMime
	// CF sends the former, Google sends the latter.
	case jsonMimeType, "application/x-javascript; charset=UTF-8":
		return jsonMime
	default:
		return badMime
	}
}

const (
	msgMimeType  = "application/dns-message"
	jsonMimeType = "application/dns-json"
)

type config struct {
	client *http.Client
	json   bool
	get    bool
	chatty bool
	log    *log.Logger
}

func (c *config) logf(format string, args ...interface{}) {
	if c.chatty {
		c.log.Printf(format, args...)
	}
}

func (c *config) api() string {
	if c.json {
		return "JSON"
	}
	return "RFC 8484"
}

func (c *config) query(ctx context.Context, srv *url.URL, m *dns.Msg) (*query, error) {
	if !c.json {
		p, err := m.Pack()
		if err != nil {
			return nil, err
		}
		q := &query{
			method: http.MethodPost,
		}
		if c.get {
			v := make(url.Values)
			v.Set("dns", b64(p))
			srv = &(*srv)
			srv.RawQuery = v.Encode()
			q.method = http.MethodGet
		} else {
			q.body = bytes.NewReader(p)
		}
		q.server = srv
		if err := c.do(ctx, q); err != nil {
			return nil, err
		}
		return q, nil
	}

	mq := m.Question[0]

	v := make(url.Values)
	if m.CheckingDisabled {
		v.Set("cd", "true")
	}
	if hasDO(m) {
		v.Set("do", "true")
	}
	v.Set("ct", jsonMimeType)
	v.Set("name", mq.Name)
	v.Set("type", dns.TypeToString[mq.Qtype])

	// Google's DoH supports extra options that Cloudflare's DNS rejects.
	if gdns(srv) {
		if s := clientSubnet(m); s != "" {
			v.Set("edns_client_subnet", s)
		}
		v.Set("random_padding", padding())
	}

	srv = &(*srv)
	srv.RawQuery = v.Encode()

	q := &query{
		server: srv,
		method: http.MethodGet,
	}
	if err := c.do(ctx, q); err != nil {
		return nil, err
	}
	return q, nil
}

func gdns(u *url.URL) bool {
	return strings.Contains(u.Host, "dns.google")
}

func hasDO(m *dns.Msg) bool {
	opt := m.IsEdns0()
	return opt != nil && opt.Do()
}

func clientSubnet(m *dns.Msg) string {
	opt := m.IsEdns0()
	if opt == nil {
		return ""
	}
	for _, o := range opt.Option {
		if o.Option() == dns.EDNS0SUBNET {
			return o.String()
		}
	}
	return ""
}

func padding() string {
	const (
		min = 12
		max = 256
	)
	buf := make([]byte, intn(max-min)+1)
	_, err := rand.Read(buf)
	if err != nil {
		panic(err)
	}
	return b64(buf)
}

func intn(n int) int {
	x, err := rand.Int(rand.Reader, big.NewInt(int64(n)))
	if err != nil {
		panic(err)
	}
	return int(x.Int64())
}

type query struct {
	server *url.URL
	method string
	body   io.Reader
	r      *dns.Msg
	start  time.Time
	rtt    time.Duration
	size   int
}

func (q *query) String() string {
	var b strings.Builder
	fmt.Fprintf(&b, "%s\n", q.r.String())
	fmt.Fprintf(&b, ";; Query time: %s\n", q.rtt.Round(1*time.Millisecond))
	fmt.Fprintf(&b, ";; SERVER: %s\n", q.server.Host)
	fmt.Fprintf(&b, ";; WHEN: %s\n", q.start.Format(time.UnixDate))
	fmt.Fprintf(&b, ";; MSG SIZE recvd: %d\n", q.size)
	b.WriteByte('\n')
	return b.String()
}

func (c *config) do(ctx context.Context, q *query) error {
	c.logf("using API %q (%s) to query %s",
		c.api(), q.method, q.server.String())

	req, err := http.NewRequestWithContext(ctx,
		q.method, q.server.String(), q.body)
	if err != nil {
		return err
	}

	req.Header.Set("Content-Type", msgMimeType)
	req.Header.Set("Accept", msgMimeType)

	q.start = time.Now()

	client := c.client
	if client == nil {
		client = http.DefaultClient
	}
	resp, err := client.Do(req)
	if err != nil {
		return err
	}
	defer closeBody(resp.Body)

	if code := resp.StatusCode; code != http.StatusOK {
		if code == http.StatusBadRequest && c.chatty {
			io.Copy(os.Stdout, resp.Body)
		}
		return fmt.Errorf("server returned HTTP %d error: %q",
			resp.StatusCode, resp.Status)
	}

	ct := resp.Header.Get("Content-Type")
	mt := sniffMime(ct)

	var maxSize int64
	switch mt {
	case msgMime:
		maxSize = 65535 // RFC 8484 §6.
	case jsonMime:
		maxSize = 10 << 20
	default:
		return fmt.Errorf("unexpected Content-Type: %q", ct)
	}

	data, err := ioutil.ReadAll(io.LimitReader(resp.Body, maxSize))
	if err != nil {
		return err
	}
	q.size = len(data)
	q.rtt = time.Since(q.start)

	switch mt {
	case msgMime:
		q.r = new(dns.Msg)
		if err := q.r.Unpack(data); err != nil {
			return err
		}
	case jsonMime:
		if c.chatty {
			var buf bytes.Buffer
			json.Indent(&buf, data, "  ", "    ")
			c.logf("response: %s", buf.Bytes())
		}
		var v jsonResp
		err := json.Unmarshal(data, &v)
		if err != nil {
			return err
		}
		q.r, err = v.msg()
		if err != nil {
			return err
		}
	default:
		panic("unreachable")
	}
	return nil
}

func closeBody(r io.ReadCloser) error {
	io.Copy(ioutil.Discard, r)
	return r.Close()
}

type jsonResp struct {
	Status   int  `json:"Status"`
	TC       bool `json:"TC"`
	RD       bool `json:"RD"`
	RA       bool `json:"RA"`
	AD       bool `json:"AD"`
	CD       bool `json:"CD"`
	Question []struct {
		Name string `json:"name"`
		Type uint16 `json:"type"`
	} `json:"Question"`
	Answer []struct {
		Name string `json:"name"`
		Type uint16 `json:"type"`
		TTL  uint32 `json:"ttl"`
		Data string `json:"data"`
	} `json:"Answer"`
}

func (r *jsonResp) msg() (*dns.Msg, error) {
	m := &dns.Msg{
		MsgHdr: dns.MsgHdr{
			Truncated:          r.TC,
			RecursionDesired:   r.RD,
			RecursionAvailable: r.RA,
			AuthenticatedData:  r.AD,
			CheckingDisabled:   r.CD,
			Rcode:              r.Status,
		},
	}
	for _, q := range r.Question {
		_, ok := dns.TypeToString[q.Type]
		if !ok {
			return nil, fmt.Errorf("unknown query type: %d", q.Type)
		}
		m.Question = append(m.Question, dns.Question{
			Name:   q.Name,
			Qtype:  q.Type,
			Qclass: dns.ClassINET,
		})
	}
	for _, a := range r.Answer {
		t, ok := dns.TypeToString[a.Type]
		if !ok {
			return nil, fmt.Errorf("unknown query type: %d", a.Type)
		}
		data := fmt.Sprintf("%s IN %d %s %s", a.Name, a.TTL, t, a.Data)
		if !strings.HasSuffix(data, "\n") {
			data += "\n"
		}
		zp := dns.NewZoneParser(strings.NewReader(data), ".", "")
		zp.SetDefaultTTL(a.TTL)
		zp.SetIncludeAllowed(false)
		rr, _ := zp.Next()
		if err := zp.Err(); err != nil {
			return nil, err
		}
		m.Answer = append(m.Answer, rr)
	}
	return m, nil
}

type uint16Flag uint16

var _ flag.Getter = (*uint16Flag)(nil)

func (i *uint16Flag) Set(s string) error {
	v, err := strconv.ParseUint(s, 0, 16)
	if err != nil {
		return err
	}
	*i = uint16Flag(v)
	return err
}

func (i *uint16Flag) Get() interface{} {
	return uint16(*i)
}

func (i *uint16Flag) String() string {
	return strconv.FormatUint(uint64(*i), 10)
}

func up(s string) string {
	return strings.ToUpper(s)
}

func b64(p []byte) string {
	return base64.RawURLEncoding.EncodeToString(p)
}

type syncWriter struct {
	mu sync.Mutex
	w  io.Writer
}

var _ io.Writer = (*syncWriter)(nil)

func (w *syncWriter) Write(p []byte) (int, error) {
	w.mu.Lock()
	defer w.mu.Unlock()

	return w.w.Write(p)
}

func (w *syncWriter) WriteStrings(s string) (int, error) {
	w.mu.Lock()
	defer w.mu.Unlock()

	return io.WriteString(w.w, s)
}
