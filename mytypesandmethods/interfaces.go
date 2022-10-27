package gocodebook

import (
	"io"
	"time"
)

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
