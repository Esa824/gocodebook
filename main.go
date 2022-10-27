package main

import (
	"flag"
	"fmt"
	"golang.org/x/net/html"
	"gopl.io/ch7/eval"
	"io"
	"io/ioutil"
	"log"
	"net/http"
	"os"
	"regexp"
	"runtime"
	"strings"
	"sync"
	//"testing"
	"encoding/xml"
	mytypes "github.com/esa1234567/gocodebook/mytypesandmethods"
	"text/tabwriter"
	"text/template"
	"time"
)

func sqaures() func() int {
	var x int
	return func() int {
		x++
		return x * x
	}
}

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

/*
	 func CelsiusFlag(name string, value Celsius, usage string) *Celsius {
		f := celsiusFlag{value}
		flag.CommandLine.Var(&f, name, usage)
		return &f.Celsius
	}
*/

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
	var root *mytypes.Tree
	for _, v := range values {
		root = add(root, v)
	}
	appendValues(values[:0], root)
}
func appendValues(values []int, t *mytypes.Tree) []int {
	if t != nil {
		values = appendValues(values, t.Left)
		values = append(values, t.Value)
		values = appendValues(values, t.Right)
	}
	return values
}
func add(t *mytypes.Tree, value int) *mytypes.Tree {
	if t == nil {
		t = new(mytypes.Tree)
		t.Value = value
		return t
	}
	if value < t.Value {
		t.Left = add(t.Left, value)
	} else {
		t.Right = add(t.Right, value)
	}
	return t
}

func printTracks(tracks []*mytypes.Track) {
	const format = "%v\t%v\t%v\t%v\t%v\t\n"
	tw := new(tabwriter.Writer).Init(os.Stdout, 0, 8, 2, ' ', 0)
	fmt.Fprintf(tw, format, "Title", "Artist", "Album", "Year", "Length")
	fmt.Fprintf(tw, format, "-----", "------", "-----", "----", "------")
	for _, t := range tracks {
		fmt.Fprintf(tw, format, t.Title, t.Artist, t.Album, t.Year, t.Length)
	}
	tw.Flush()
}

/* func sqlQuote(x interface{}) string {
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
} */

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
