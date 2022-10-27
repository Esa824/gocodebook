package main

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
