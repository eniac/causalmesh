package common

import (
	"github.com/stretchr/testify/assert"
	"testing"
)

func TestMeta1(t *testing.T) {
	m1 := Meta{Key: "k1", Value: "v1", Vc: VC{1, 2}, Deps: map[string]VC{"k2": VC{1, 1}}}
	m2 := Meta{Key: "k1", Value: "v2", Vc: VC{2, 2}, Deps: map[string]VC{"k2": VC{0, 2}}}
	m3 := MergeMeta(&m1, &m2)
	// m1, m2 should not be changed
	assert.Equal(t, m1.Deps, map[string]VC{"k2": VC{1, 1}})
	assert.Equal(t, m2.Deps, map[string]VC{"k2": VC{0, 2}})
	MergeIntoMeta(&m1, &m2)
	// m2 should not be changed
	assert.Equal(t, m2.Deps, map[string]VC{"k2": VC{0, 2}})
	assert.Equal(t, m1, m3)
	assert.Equal(t, m3.Value, "v2")
	assert.Equal(t, m3.Vc, VC{2, 2})
	assert.Equal(t, m3.Deps, map[string]VC{"k2": VC{1, 2}})
}

func TestMeta2(t *testing.T) {
	m1 := Meta{Key: "k1", Value: "v1", Vc: VC{1, 2}, Deps: map[string]VC{"k2": VC{1, 1}}}
	m2 := Meta{Key: "k1", Value: "v2", Vc: VC{2, 0}, Deps: map[string]VC{"k2": VC{0, 2}}}
	m2Cp := Meta{Key: "k1", Value: "v2", Vc: VC{2, 0}, Deps: map[string]VC{"k2": VC{0, 2}}}
	m3 := MergeMeta(&m1, &m2)
	MergeIntoMeta(&m1, &m2)
	assert.Equal(t, m1, m3)
	assert.Equal(t, m2, m2Cp)
	assert.Equal(t, m3.Value, "v2")
	assert.Equal(t, m3.Vc, VC{2, 2})
	assert.Equal(t, m3.Deps, map[string]VC{"k2": VC{1, 2}})
}

func TestMeta3(t *testing.T) {
	m1 := Meta{Key: "k1", Value: "v1", Vc: VC{1, 1}, Deps: map[string]VC{}}
	m2 := Meta{Key: "k1", Value: "v1", Vc: VC{2, 0}, Deps: map[string]VC{}}
	m3 := MergeMeta(&m1, &m2)
	m3.Deps = map[string]VC{"k1": VC{1, 1}}
	assert.Equal(t, m1.Deps, map[string]VC{})
}

func TestInsertOrMergeMeta(t *testing.T) {
	m1 := Meta{Key: "k1", Value: "v1", Vc: VC{1, 2}, Deps: map[string]VC{"k1": VC{1, 1}, "k2": VC{1, 1}}}
	m2 := Meta{Key: "k1", Value: "v2", Vc: VC{2, 0}, Deps: map[string]VC{"k1": VC{0, 2}}}
	mm := map[string]*Meta{"k1": &m1}
	InsertOrMergeMeta(&mm, "k1", &m2)
	// m2 should not be changed
	assert.Equal(t, m2.Deps, map[string]VC{"k1": VC{0, 2}})
	// m1 is changed
	assert.Equal(t, m1.Deps, map[string]VC{"k1": VC{1, 2}, "k2": VC{1, 1}})
	assert.Equal(t, mm["k1"].Deps, map[string]VC{"k1": VC{1, 2}, "k2": VC{1, 1}})
}
