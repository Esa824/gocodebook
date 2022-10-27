package main

import (
	"bytes"
	"encoding/json"
	"flag"
	"fmt"
	"golang.org/x/net/html"
	"gopl.io/ch7/eval"
	"image/color"
	"io"
	"io/ioutil"
	"log"
	"math"
	"net/http"
	"net/url"
	"os"
	"regexp"
	"runtime"
	"strings"
	"sync"
	//"testing"
	"encoding/xml"
	"text/tabwriter"
	"text/template"
	"time"
)

const IssuesURL = "https://api.github/search/issues"

type IssuesSearchResult struct {
	TotalCount int `json:"total_count"`
	items      []*Issue
}
type Issue struct {
	Number    int
	HTMLURL   string `json:"html_url"`
	Title     string
	State     string
	User      *User
	CreatedAt time.Time
	Body      string
}
type Track struct {
	Title  string
	Artist string
	Album  string
	Year   int
	Length time.Duration
}
type Buffer struct {
	buf     []byte
	initial [64]byte
	/* ... */
}
type Point struct{ X, Y float64 }
type ColoredPoint struct {
	Point
	Color color.RGBA
}
type Counter struct{ n int }

type Logger struct {
	flags  int
	prefix string
	// ...
}
type celsiusFlag struct{ Celsius }
type IntList struct {
	Value int
	Tail  *IntList
}
type IntSet struct {
	words []uint64
}
type tree struct {
	value       int
	left, right *tree
}
type Rocket struct {
	/* ... */
}

func (r *Rocket) Launch() {
	/* ... */
}

type Node struct {
	Type                    NodeType
	Data                    string
	Attr                    []Attribute
	FirstChild, Nextsibling *Node
}
type Elemant struct {
	Type     xml.Name
	Attr     []xml.Attr
	Children []Node
}
type NodeType int32

const (
	ErrorNode NodeType = iota
	TextNode
	DocumentNode
	ElemantNode
	CommentNode
	DoctypeNode
)

type Attribute struct {
	Key, val string
}

type User struct {
	Login   string
	HTMLURL string `json:"html_url"`
}
type customSort struct {
	t    []*Track
	less func(x, y *Track) bool
}
type unary struct {
	op rune
	x  Expr
}
type binary struct {
	op   rune
	x, y Expr
}
type call struct {
	fn   string
	args []Expr
}
type PathError struct {
	Op   string
	Path string
	Err  error
}
type Artifact interface {
	Title() string
	Creators() []string
	Created() time.Time
}
type Text interface {
	Pages() int
	Words() int
	PageSize() int
}
type Audio interface {
	Stream() (io.ReadCloser, error)
	RunningTime() time.Duration
	Format() string
}

type Video interface {
	Stream() (io.ReadCloser, error)
	RunningTime() time.Duration
	Format() string
	Resultion() (x, y int)
}

type Streamer interface {
	Stream() (io.ReadCloser, error)
	RunningTime() time.Duration
	Format() string
}
type Value interface {
	String() string
	Set(string) error
}
type Expr interface {
	Eval(env Env) float64
	Check(vars map[Var]bool) error
}
type Nodexml interface{}

func sqaures() func() int {
	var x int
	return func() int {
		x++
		return x * x
	}
}
func (list *IntList) sum() int {
	if list == nil {
		return 0
	}
	return list.Value + list.Tail.sum()
}

type Var string
type CharData string
type literal float64

type Values map[string][]string

type Env map[Var]float64

func (v Values) Get(key string) string {
	if vs := v[key]; len(vs) > 0 {
		return vs[0]
	}
	return " "
}
func (v Values) Add(key, value string) {
	v[key] = append(v[key], value)
}

func (v Var) Eval(env Env) float64 {
	return env[v]
}
func (v Var) Check(vars map[Var]bool) error {
	vars[v] = true
	return nil
}
func (l literal) Eval(_ Env) float64 {
	return float64(l)
}
func (literal) Check(vars map[Var]bool) error {
	return nil
}
func (u unary) Eval(env Env) float64 {
	switch u.op {
	case '+':
		return +u.x.Eval(env)
	case '-':
		return -u.x.Eval(env)
	}
	panic(fmt.Sprintf("unsupported unary operator %q", u.op))
}
func (u unary) Check(vars map[Var]bool) error {
	if !strings.ContainsRune("+-", u.op) {
		return fmt.Errorf("unexpected unary op %q", u.op)
	}
	return u.x.Check(vars)
}
func (e *PathError) Error() string {
	return e.Op + " " + e.Path + ": " + e.Err.Error()
}
func (b binary) Eval(env Env) float64 {
	switch b.op {
	case '+':
		return b.x.Eval(env) + b.y.Eval(env)
	case '-':
		return b.x.Eval(env) - b.y.Eval(env)
	case '*':
		return b.x.Eval(env) * b.y.Eval(env)
	case '/':
		return b.x.Eval(env) / b.y.Eval(env)
	}
	panic(fmt.Sprintf("unsupported binary operator %q", b.op))
}
func (b binary) Check(vars map[Var]bool) error {
	if !strings.ContainsRune("+-*/", b.op) {
		return fmt.Errorf("unexpected binary op %q", b.op)
	}
	if err := b.x.Check(vars); err != nil {
		return err
	}
	return b.y.Check(vars)
}
func (c call) Eval(env Env) float64 {
	switch c.fn {
	case "pow":
		return math.Pow(c.args[0].Eval(env), c.args[1].Eval(env))

	case "sqrt":
		return math.Sqrt(c.args[0].Eval(env))
	}
	panic(fmt.Sprintf("unsupported function call: %s", c.fn))
}
func (c call) Check(vars map[Var]bool) error {
	arity, ok := numParams[c.fn]
	if !ok {
		return fmt.Errorf("unknown function %q", c.fn)
	}
	if len(c.args) != arity {
		return fmt.Errorf("call to %s has %d args, want %d", c.fn, len(c.args), arity)
	}
	for _, arg := range c.args {
		if err := arg.Check(vars); err != nil {
			return err
		}
	}
	return nil
}

var numParams = map[string]int{"pow": 2, "sin": 1, "sqrt": 1}

func parseAndCheck(s string) (eval.Expr, error) {
	if s == " " {
		return nil, fmt.Errorf("empty expression")
	}
	expr, err := eval.Parse(s)
	if err != nil {
		return nil, err
	}
	vars := make(map[eval.Var]bool)
	if err := expr.Check(vars); err != nil {
		return nil, err
	}
	for v := range vars {
		if v != "x" && v != "y" && v != "r" {
			return nil, fmt.Errorf("undefined variable: %s", v)
		}
	}
	return expr, nil
}
func forEachNode(n *html.Node, pre, post func(n *html.Node)) {
	if pre != nil {
		pre(n)
	}
	for c := n.FirstChild; c != nil; c = c.NextSibling {
		forEachNode(c, pre, post)
	}
	if post != nil {
		post(n)
	}
}

/*
	 func TestEval(t *testing.T) {
		tests := []struct {
			expr string
			env  Env
			want string
		}{
			{"sqrt(A / pi)", Env{"A": 87616, "pi": math.Pi}, "167"},
			{"pow(x, 3) + pow(y, 3)", Env{"x": 12, "y": 1}, "1729"},
			{"pow(x, 3) + pow(y, 3)", Env{"x": 9, "y": 10}, "1729"},
			{"5 / 9 * (F - 32)", Env{"F": -40}, "-40"},
			{"5 / 9 * (F - 32)", Env{"F": 32}, "0"},
			{"5 / 9 * (F - 32)", Env{"F": 212}, "100"},
		}
		var prevExpr string
		for _, test := range tests {
			if test.expr != prevExpr {
				fmt.Printf("\n%s\n", test.expr)
				prevExpr = test.expr
			}
			expr, err := Parse(test.expr)
			if err != nil {
				t.Error(err)
				continue
			}
			got := fmt.Sprintf("%.6g", expr.Eval(test.env))
			fmt.Printf("\t%v => %s\n", test.env, got)
			if got != test.want {
				t.Errorf("%s.Eval() in %s = %q, want %q\n", test.expr, test.env, got, test.want)
			}
		}
	}
*/
func bigSlowOperation() {
	defer trace("bigSlowOperation")()
	time.Sleep(10 * time.Second)
}
func trace(msg string) func() {
	start := time.Now()
	log.Printf("enter %s", msg)
	return func() {
		log.Printf("exit %s (%s)", msg, time.Since(start))
	}
}

type Path []Point

func (path Path) Distance() float64 {
	sum := 0.0
	for i := range path {
		if i > 0 {
			sum += path[i-1].Distance(path[i])
		}
	}
	return sum
}
func (path Path) TransalateBy(offset Point, add bool) {
	var op func(p, q Point) Point
	if add {
		op = Point.Add
	} else {
		op = Point.Sub
	}
	for i := range path {
		path[i] = op(path[i], offset)
	}
}
func ReadFile(filename string) ([]byte, error) {
	f, err := os.Open(filename)
	if err != nil {
		return nil, err
	}
	defer f.Close()
	return ioutil.ReadAll(f)
}

var mu sync.Mutex
var m = make(map[string]int)

func lookup(key string) int {
	mu.Lock()
	defer mu.Unlock()
	return m[key]
}
func (p Point) Distance(q Point) float64 {
	return math.Hypot(q.X-p.X, q.Y-p.Y)
}
func (p Point) Add(q Point) Point {
	return Point{p.X + q.X, p.Y + q.Y}
}
func (p Point) Sub(q Point) Point {
	return Point{p.X - q.X, p.Y - q.Y}
}
func Distance(p, q Point) float64 {
	return math.Hypot(q.X-p.X, q.Y-p.Y)
}

type Celsius float64
type Fahrenheit float64

const (
	AbsoluteZeroC Celsius = -273.15
	FreezingC     Celsius = 0
	BoilingC      Celsius = 100
)

func CTof(c Celsius) Fahrenheit { return Fahrenheit(c*9/5 + 32) }
func FToc(f Fahrenheit) Celsius { return Celsius((f - 32) * 5 / 9) }
func (f *celsiusFlag) Set(s string) error {
	var unit string
	var value float64
	fmt.Sscanf(s, "%f%s", &value, &unit)
	switch unit {
	case "C", "oC":
		f.Celsius = Celsius(value)
		return nil
	case "F", "oF":
		f.Celsius = FToc(Fahrenheit(value))
		return nil
	}
	return fmt.Errorf("invalid temperature %q", s)
}

/*
	 func CelsiusFlag(name string, value Celsius, usage string) *Celsius {
		f := celsiusFlag{value}
		flag.CommandLine.Var(&f, name, usage)
		return &f.Celsius
	}
*/
func (p *Point) ScaleBy(factor float64) {
	p.X *= factor
	p.Y *= factor
}
func (c *Counter) N() int     { return c.n }
func (c *Counter) Increment() { c.n++ }
func (c *Counter) Reset()     { c.n = 0 }

func (b *Buffer) Grow(n int) {
	if b.buf == nil {
		b.buf = b.initial[:0]
	}
	if len(b.buf)+n > cap(b.buf) {
		buf := make([]byte, len(b.buf), 2*cap(b.buf)+n)
		copy(buf, b.buf)
		b.buf = buf
	}
}

type ByteCounter int

func (c *ByteCounter) Write(p []byte) (int, error) {
	*c += ByteCounter(len(p))
	return len(p), nil
}
func (s *IntSet) Has(x int) bool {
	word, bit := x/64, uint(x%64)
	return word < len(s.words) && s.words[word]&(1<<bit) != 0
}
func (s *IntSet) Remove(x int) {
	var newset = new(IntSet)
	word, bit := x/64, uint(x%64)
	fmt.Println(newset.Has(0))
	if s.words[word]&(1<<bit) != 0 {
		var access int = int(s.words[word] & (1 << bit))
		println(access)
	}
}
func (s *IntSet) Len() int {
	return len(s.words) / 64
}

func (l *Logger) FLags() int              { return 0 }
func (l *Logger) SetFlags(flag int)       {}
func (l *Logger) Prefix() string          { return "" }
func (l *Logger) SetPrefix(prefix string) {}
func (s *IntSet) Add(x ...int) {
	for i := range x {
		word, bit := x[i]/64, uint(x[i]%64)
		for word >= len(s.words) {
			s.words = append(s.words, 0)
		}
		s.words[word] |= 1 << bit
	}
}

func (s *IntSet) Copy() *IntSet {
	set := s
	return set
}
func (s *IntSet) UnionWith(t *IntSet) {
	for i, tword := range t.words {
		if i < len(s.words) {
			s.words[i] |= tword
		} else {
			s.words = append(s.words, tword)
		}
	}
}

func (x customSort) Len() int {
	return len(x.t)
}
func (x customSort) Less(i, j int) bool {
	return x.less(x.t[i], x.t[j])
}

func (x customSort) Swap(i, j int) {
	x.t[i], x.t[j] = x.t[j], x.t[i]
}
func (s *IntSet) String() string {
	var buf bytes.Buffer
	buf.WriteByte('{')
	for i, word := range s.words {
		if word == 0 {
			continue
		}
		for j := 0; j < 64; j++ {
			if word&(1<<uint(j)) != 0 {
				if buf.Len() > len("{") {
					buf.WriteByte(' ')
				}
				fmt.Fprintf(&buf, "%d", 64*i+j)
			}
		}
	}
	buf.WriteByte('}')
	return buf.String()
}
func title(url string) error {
	resp, err := http.Get(url)
	if err != nil {
		return err
	}
	defer resp.Body.Close()
	ct := resp.Header.Get("Content-Type")
	if ct != "text/html" && !strings.HasPrefix(ct, "text/html;") {
		resp.Body.Close()
		return fmt.Errorf("%s has type %s, not text/html", url, ct)
	}
	doc, err := html.Parse(resp.Body)
	resp.Body.Close()
	if err != nil {
		return fmt.Errorf("parsing %s as HTML: %v", url, err)
	}
	visitNode := func(n *html.Node) {
		if n.Type == html.ElementNode && n.Data == "title" && n.FirstChild != nil {
			fmt.Println(n.FirstChild.Data)
		}
	}
	forEachNode(doc, visitNode, nil)
	return nil
}

/*
func Fprintf(w io.Writer, format string, args ...interface{}) (int, error)

	func Printf(format string, args ...interface{}) (int, error) {
		return Fprintf(os.Stdout, format, args...)
	}

	func Sprintf(format string, args ...interface{}) string {
		var buf bytes.Buffer
		Fprintf(&buf, format, args...)
		return buf.String()
	}
*/
func Sort(values []int) {
	var root *tree
	for _, v := range values {
		root = add(root, v)
	}
	appendValues(values[:0], root)
}
func appendValues(values []int, t *tree) []int {
	if t != nil {
		values = appendValues(values, t.left)
		values = append(values, t.value)
		values = appendValues(values, t.right)
	}
	return values
}
func add(t *tree, value int) *tree {
	if t == nil {
		t = new(tree)
		t.value = value
		return t
	}
	if value < t.value {
		t.left = add(t.left, value)
	} else {
		t.right = add(t.right, value)
	}
	return t
}

type StringSlice []string

func (p StringSlice) Len() int {
	return p.Len()
}
func (p StringSlice) Less(i, j int) bool {
	return p[i] < p[j]
}
func (p StringSlice) Swap(i, j int) {
	p[i], p[j] = p[j], p[i]
}

type byArtist []*Track

func (x byArtist) Len() int           { return len(x) }
func (x byArtist) Less(i, j int) bool { return x[i].Artist < x[j].Artist }
func (x byArtist) Swap(i, j int)      { x[i], x[j] = x[j], x[i] }
func printTracks(tracks []*Track) {
	const format = "%v\t%v\t%v\t%v\t%v\t\n"
	tw := new(tabwriter.Writer).Init(os.Stdout, 0, 8, 2, ' ', 0)
	fmt.Fprintf(tw, format, "Title", "Artist", "Album", "Year", "Length")
	fmt.Fprintf(tw, format, "-----", "------", "-----", "----", "------")
	for _, t := range tracks {
		fmt.Fprintf(tw, format, t.Title, t.Artist, t.Album, t.Year, t.Length)
	}
	tw.Flush()
}
func sqlQuote(x interface{}) string {
	switch x := x.(type) {
	case nil:
		return "NULL"
	case int, uint:
		return fmt.Sprintf("%d", x) // x has type interface{} here.
	case bool:
		if x {
			return "TRUE"
		}
		return "FALSE"
	case string:
		return sqlQuoteString(x) // (not shown)
	default:
		panic(fmt.Sprintf("unexpected type %T: %v", x, x))
	}
}
func SearchIssues(terms []string) (*IssuesSearchResult, error) {
	q := url.QueryEscape(strings.Join(terms, " "))
	resp, err := http.Get(IssuesURL + "?q=" + q)
	if err != nil {
		return nil, err
	}
	if resp.StatusCode != http.StatusOK {
		resp.Body.Close()
		return nil, fmt.Errorf("search query failed: %s", resp.Status)
	}
	var result IssuesSearchResult
	if err := json.NewDecoder(resp.Body).Decode(&result); err != nil {
		resp.Body.Close()
		return nil, err
	}
	resp.Body.Close()
	return &result, nil
}

var report = template.Must(template.New("issuelist").Funcs(template.FuncMap{"daysAgo": daysAgo}).Parse(templ))

func Add(x int, y int) int   { return x + y }
func Sub(x, y int) (z int)   { z = x - y; return }
func First(x int, _ int) int { return x }
func Zero(int, int) int      { return 0 }
func visit(links []string, n *html.Node) []string {
	if n.Type == html.ElementNode && n.Data == "a" {
		for _, a := range n.Attr {
			if a.Key == "href" {
				links = append(links, a.Val)
			}
		}
	}
	for c := n.FirstChild; c != nil; c = c.NextSibling {
		links = visit(links, c)
	}
	return links
}
func soleTitle(doc *html.Node) (title string, err error) {
	type bailout struct{}
	defer func() {
		switch p := recover(); p {
		case nil:
		case bailout{}:
			err = fmt.Errorf("multiple title elemants")
		default:
			panic(p)
		}
	}()
	forEachNode(doc, func(n *html.Node) {
		if n.Type == html.ElementNode && n.Data == "title" && n.FirstChild != nil {
			if title != " " {
				panic(bailout{})
			}
			title = n.FirstChild.Data
		}
	}, nil)
	if title == " " {
		return " ", fmt.Errorf("no title elemant")
	}
	return title, nil
}
func sum(vals ...int) int {
	total := 0
	for _, val := range vals {
		total += val
	}
	return total
}

var tracks = []*Track{
	{"Go", "Deliah", "From the Roots Up", 2012, length("3m38s")},
	{"Go", "Moby", "Moby", 1992, length("3m37s")},
	{"Go Ahead", "Alica Keys", "As I Am", 2007, length("4m36s")},
	{"Ready 2 Go", "Martin Solveig", "Smash", 2011, length("4m24s")},
}

func length(s string) time.Duration {
	d, err := time.ParseDuration(s)
	if err != nil {
		panic(err)
	}
	return d
}

func MustCompile(expr string) *regexp.Regexp {
	re, err := regexp.Compile(expr)
	if err != nil {
		panic(err)
	}
	return re
}
func writeString(w io.Writer, s string) (n int, err error) {
	type stringWriter interface {
		io.Writer
		WriteString(string) (n int, err error)
	}
	if sw, ok := w.(stringWriter); ok {
		return sw.WriteString(s)
	}
	return w.Write([]byte(s))
}
func WriteHeader(w io.Writer, ContentType string) error {
	if _, err := writeString(w, "Content-Type: "); err != nil {
		return err
	}
	if _, err := writeString(w, ContentType); err != nil {
		return err
	}
	return nil
}

var period = flag.Duration("period", 1*time.Second, "sleep period")

const debug = true

func main() {
	dec := xml.NewDecoder(os.Stdin)
	var stack []string // stack of element names
	for {
		tok, err := dec.Token()
		if err == io.EOF {
			break
		} else if err != nil {
			fmt.Fprintf(os.Stderr, "xmlselect: %v\n", err)
			os.Exit(1)
		}
		switch tok := tok.(type) {
		case xml.StartElement:
			stack = append(stack, tok.Name.Local) // push
		case xml.EndElement:
			stack = stack[:len(stack)-1] // pop
		case xml.CharData:
			if containsAll(stack, os.Args[1:]) {
				fmt.Printf("%s:     %s\n", strings.Join(stack, " "), tok)
			}
		}
	}
}
func containsAll(x, y []string) bool {
	for len(y) <= len(x) {
		if len(y) == 0 {
			return true
		}
		if x[0] == y[0] {
			y = y[1:]
		}
		x = x[1:]
	}
	return false
}

type dollars float32

func (d dollars) String() string {
	return fmt.Sprintf("$%.2f", d)
}

type database map[string]dollars

func (db database) list(w http.ResponseWriter, req *http.Request) {
	for item, price := range db {
		fmt.Fprintf(w, "%s: %s\n", item, price)
	}
}

/*
	 func plot(w http.ResponseWriter, r *http.Request) {
		r.ParseForm()
		expr, err := parseAndCheck(r.Form.Get("expr"))
		if err != nil {
			http.Error(w, "bad expr: "+err.Error(), http.StatusBadRequest)
			return
		}
		w.Header().Set("Content-Type", "image/svg+xml")
		surface(w, func(x, y float64) float64 {
			r := math.Hypot(x, y)
			return expr.Eval(eval.Env{"x": x, "y": y, "r": r})
		})
	}
*/
func (db database) price(w http.ResponseWriter, req *http.Request) {
	item := req.URL.Query().Get("item")
	price, ok := db[item]
	if !ok {
		w.WriteHeader(http.StatusNotFound)
		fmt.Fprintf(w, "no such item: %q\n", item)
		return
	}
	fmt.Fprintf(w, "%s\n", price)
}
func (db database) ServeHTTP(w http.ResponseWriter, req *http.Request) {
	switch req.URL.Path {
	case "/list":
		for item, price := range db {
			fmt.Fprintf(w, "%s: %s\n", item, price)
		}
	case "/price":
		item := req.URL.Query().Get("item")
		price, ok := db[item]
		if !ok {
			w.WriteHeader(http.StatusNotFound)
			fmt.Fprintf(w, "no such item: %q\n", item)
			return
		}
		fmt.Fprintf(w, "%s\n", price)
	default:
		w.WriteHeader(http.StatusNotFound)
		fmt.Fprintf(w, "no such page: %s\n", req.URL)
	}
}
func ff(out io.Writer) {
	if out != nil {
		out.Write([]byte("done!\n"))
	}
}
func printStack() {
	var buf [4096]byte
	n := runtime.Stack(buf[:], false)
	os.Stdout.Write(buf[:n])
}
func f(x int) {
	fmt.Printf("f(%d)\n", x+0/x)
	defer fmt.Printf("defer %d\n", x)
	f(x - 1)
}
func findLinks(url string) ([]string, error) {
	resp, err := http.Get(url)
	if err != nil {
		return nil, err
	}
	if resp.StatusCode != http.StatusOK {
		resp.Body.Close()
		return nil, fmt.Errorf("getting %s: %s", url, resp.Status)
	}
	doc, err := html.Parse(resp.Body)
	resp.Body.Close()
	if err != nil {
		return nil, fmt.Errorf("parsing %s as HTML: %v", url, err)
	}
	return visit(nil, doc), nil
}
func outline(stack []string, n *html.Node) {
	if n.Type == html.ElementNode {
		stack = append(stack, n.Data)
		fmt.Println(stack)
	}
	for c := n.FirstChild; c != nil; c = c.NextSibling {
		outline(stack, c)
	}
}

const templ = `{{.TotalCount}} issues:
{{range     .Items}}-------------------------------------
---
Number: {{.Number}}
User:  {{.User.Login}}
Title: {{.Title | printf "%.64s"}}
Age: {{.CreatedAt | daysAgo}} days
{{end}}`

func daysAgo(t time.Time) int {
	return int(time.Since(t).Hours() / 24)
}
