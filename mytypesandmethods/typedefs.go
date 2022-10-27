package gocodebook

const IssuesURL = "https://api.github/search/issues"

type NodeType int32

type Var string
type CharData string
type literal float64

type Values map[string][]string

type Env map[Var]float64

type Path []Point

type Celsius float64
type Fahrenheit float64
type ByteCounter int

type StringSlice []string

type byArtist []*Track

type dollars float32

type database map[string]dollars

const (
	AbsoluteZeroC Celsius = -273.15
	FreezingC     Celsius = 0
	BoilingC      Celsius = 100
)

var numParams = map[string]int{"pow": 2, "sin": 1, "sqrt": 1}

const (
	ErrorNode NodeType = iota
	TextNode
	DocumentNode
	ElemantNode
	CommentNode
	DoctypeNode
)

var tracks = []*Track{
	{"Go", "Deliah", "From the Roots Up", 2012, length("3m38s")},
	{"Go", "Moby", "Moby", 1992, length("3m37s")},
	{"Go Ahead", "Alica Keys", "As I Am", 2007, length("4m36s")},
	{"Ready 2 Go", "Martin Solveig", "Smash", 2011, length("4m24s")},
}
