package gocodebook

import (
	"encoding/xml"
	"image/color"
	"time"
)

type IssuesSearchResult struct {
	TotalCount int `json:"total_count"`
	Items      []*Issue
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
	Buf     []byte
	Initial [64]byte
	/* ... */
}
type Point struct{ X, Y float64 }
type ColoredPoint struct {
	Point
	Color color.RGBA
}
type Counter struct{ n int }

type Logger struct {
	Flags       int
	PrefixField string
	// ...
}
type CelsiusFlag struct{ Celsius }
type IntList struct {
	Value int
	Tail  *IntList
}
type IntSet struct {
	Words []uint64
}
type Tree struct {
	Value       int
	Left, Right *Tree
}
type Rocket struct {
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
type Attribute struct {
	Key, Val string
}

type User struct {
	Login   string
	HTMLURL string `json:"html_url"`
}
type CustomSort struct {
	T    []*Track
	Less func(x, y *Track) bool
}
type Unary struct {
	Op rune
	X  Expr
}
type Binary struct {
	Op   rune
	X, Y Expr
}
type Call struct {
	Fn   string
	Args []Expr
}
type PathError struct {
	Op   string
	Path string
	Err  error
}
