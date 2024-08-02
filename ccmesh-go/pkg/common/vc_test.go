package common

import (
	"github.com/stretchr/testify/assert"
	"testing"
)

func TestVC1(t *testing.T) {
	a := VC{1, 2}
	b := VC{1, 2}

	assert.Equal(t, Compare(a, b), 0)
	assert.Equal(t, HappensBefore(a, b), false)
	assert.Equal(t, HappensBefore(b, a), false)
	assert.Equal(t, Concurrent(a, b), false)
}

func TestVC2(t *testing.T) {
	a := VC{2, 1}
	b := VC{1, 3}

	assert.Equal(t, Compare(a, b), 2)
	assert.Equal(t, HappensBefore(a, b), false)
	assert.Equal(t, HappensBefore(b, a), false)
	assert.Equal(t, Concurrent(a, b), true)
	assert.Equal(t, Privilege(a, b), true)
}

func TestVC3(t *testing.T) {
	a := VC{1, 2}
	b := VC{1, 3}

	assert.Equal(t, Compare(a, b), -1)
	assert.Equal(t, HappensBefore(a, b), true)
	assert.Equal(t, HappensBefore(b, a), false)
	assert.Equal(t, Concurrent(a, b), false)
}

func TestVC4(t *testing.T) {
	a := VC{2, 1}
	b := VC{1, 3}
	c := MergeVC(&a, &b)
	assert.Equal(t, c, VC{2, 3})
	// a, b are not changed
	assert.Equal(t, a, VC{2, 1})
	assert.Equal(t, b, VC{1, 3})

	MergeIntoVC(&a, &b)

	assert.Equal(t, a, c)
	assert.Equal(t, Compare(a, c), 0)
	assert.Equal(t, a, VC{2, 3})
	assert.Equal(t, b, VC{1, 3})
}

func TestInsertOrMergeVC(t *testing.T) {
	a := VC{0, 2}
	b := VC{1, 1}
	m := map[string]VC{"a": a}
	InsertOrMergeVC(&m, "a", &b)
	assert.Equal(t, m["a"], VC{1, 2})
	assert.Equal(t, a, VC{0, 2}) // a is not changed
	InsertOrMergeVC(&m, "b", &b)
	assert.Equal(t, m["b"], VC{1, 1})
	b[0] += 1
	assert.Equal(t, m["b"], VC{1, 1}) // b is not changed
}
