package gocodebook

import (
	"bytes"
	"encoding/json"
	"fmt"
	"math"
	"net/http"
	"net/url"
	"strings"
	"time"
)

func (r *Rocket) Launch() {
	/* ... */
}

func (list *IntList) sum() int {
	if list == nil {
		return 0
	}
	return list.Value + list.Tail.sum()
}

func (u Unary) Eval(env Env) float64 {
	switch u.Op {
	case '+':
		return +u.X.Eval(env)
	case '-':
		return -u.X.Eval(env)
	}
	panic(fmt.Sprintf("unsupported unary operator %q", u.Op))
}
func (u Unary) Check(vars map[Var]bool) error {
	if !strings.ContainsRune("+-", u.Op) {
		return fmt.Errorf("unexpected unary op %q", u.Op)
	}
	return u.X.Check(vars)
}
func (e *PathError) Error() string {
	return e.Op + " " + e.Path + ": " + e.Err.Error()
}
func (b Binary) Eval(env Env) float64 {
	switch b.Op {
	case '+':
		return b.X.Eval(env) + b.Y.Eval(env)
	case '-':
		return b.X.Eval(env) - b.Y.Eval(env)
	case '*':
		return b.X.Eval(env) * b.Y.Eval(env)
	case '/':
		return b.X.Eval(env) / b.Y.Eval(env)
	}
	panic(fmt.Sprintf("unsupported binary operator %q", b.Op))
}
func (b Binary) Check(vars map[Var]bool) error {
	if !strings.ContainsRune("+-*/", b.Op) {
		return fmt.Errorf("unexpected binary op %q", b.Op)
	}
	if err := b.X.Check(vars); err != nil {
		return err
	}
	return b.Y.Check(vars)
}
func (c Call) Eval(env Env) float64 {
	switch c.Fn {
	case "pow":
		return math.Pow(c.Args[0].Eval(env), c.Args[1].Eval(env))

	case "sqrt":
		return math.Sqrt(c.Args[0].Eval(env))
	}
	panic(fmt.Sprintf("unsupported function call: %s", c.Fn))
}

func (c Call) Check(vars map[Var]bool) error {
	arity, ok := numParams[c.Fn]
	if !ok {
		return fmt.Errorf("unknown function %q", c.Fn)
	}
	if len(c.Args) != arity {
		return fmt.Errorf("call to %s has %d args, want %d", c.Fn, len(c.Args), arity)
	}
	for _, arg := range c.Args {
		if err := arg.Check(vars); err != nil {
			return err
		}
	}
	return nil
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

func (f *CelsiusFlag) Set(s string) error {
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

func (p *Point) ScaleBy(factor float64) {
	p.X *= factor
	p.Y *= factor
}
func (c *Counter) N() int     { return c.n }
func (c *Counter) Increment() { c.n++ }
func (c *Counter) Reset()     { c.n = 0 }

func (b *Buffer) Grow(n int) {
	if b.Buf == nil {
		b.Buf = b.Initial[:0]
	}
	if len(b.Buf)+n > cap(b.Buf) {
		buf := make([]byte, len(b.Buf), 2*cap(b.Buf)+n)
		copy(buf, b.Buf)
		b.Buf = buf
	}
}

func (s *IntSet) Has(x int) bool {
	word, bit := x/64, uint(x%64)
	return word < len(s.Words) && s.Words[word]&(1<<bit) != 0
}
func (s *IntSet) Remove(x int) {
	var newset = new(IntSet)
	word, bit := x/64, uint(x%64)
	fmt.Println(newset.Has(0))
	if s.Words[word]&(1<<bit) != 0 {
		var access int = int(s.Words[word] & (1 << bit))
		println(access)
	}
}
func (s *IntSet) Len() int {
	return len(s.Words) / 64
}
func (s *IntSet) Copy() *IntSet {
	set := s
	return set
}
func (s *IntSet) UnionWith(t *IntSet) {
	for i, tword := range t.Words {
		if i < len(s.Words) {
			s.Words[i] |= tword
		} else {
			s.Words = append(s.Words, tword)
		}
	}
}

func (x CustomSort) Len() int {
	return len(x.T)
}
func (x CustomSort) LessMethod(i, j int) bool {
	return x.Less(x.T[i], x.T[j])
}

func (x CustomSort) Swap(i, j int) {
	x.T[i], x.T[j] = x.T[j], x.T[i]
}
func (s *IntSet) String() string {
	var buf bytes.Buffer
	buf.WriteByte('{')
	for i, word := range s.Words {
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
func (l *Logger) FLags() int              { return 0 }
func (l *Logger) SetFlags(flag int)       {}
func (l *Logger) Prefix() string          { return "" }
func (l *Logger) SetPrefix(prefix string) {}
func (s *IntSet) Add(x ...int) {
	for i := range x {
		word, bit := x[i]/64, uint(x[i]%64)
		for word >= len(s.Words) {
			s.Words = append(s.Words, 0)
		}
		s.Words[word] |= 1 << bit
	}
}
func (d dollars) String() string {
	return fmt.Sprintf("$%.2f", d)
}

func (db database) list(w http.ResponseWriter, req *http.Request) {
	for item, price := range db {
		fmt.Fprintf(w, "%s: %s\n", item, price)
	}
}
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

func (c *ByteCounter) Write(p []byte) (int, error) {
	*c += ByteCounter(len(p))
	return len(p), nil
}

func CTof(c Celsius) Fahrenheit { return Fahrenheit(c*9/5 + 32) }
func FToc(f Fahrenheit) Celsius { return Celsius((f - 32) * 5 / 9) }

func length(s string) time.Duration {
	d, err := time.ParseDuration(s)
	if err != nil {
		panic(err)
	}
	return d
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

func (p StringSlice) Len() int {
	return p.Len()
}
func (p StringSlice) Less(i, j int) bool {
	return p[i] < p[j]
}
func (p StringSlice) Swap(i, j int) {
	p[i], p[j] = p[j], p[i]
}

func (x byArtist) Len() int           { return len(x) }
func (x byArtist) Less(i, j int) bool { return x[i].Artist < x[j].Artist }
func (x byArtist) Swap(i, j int)      { x[i], x[j] = x[j], x[i] }
