package common

type Meta struct {
	Key   string        `json:"key"`
	Value string        `json:"value"`
	Vc    VC            `json:"vc"`
	Deps  map[string]VC `json:"deps"`
}

func MergeIntoMeta(mutSelf *Meta, other *Meta) {
	if mutSelf.Key != other.Key {
		panic("mismatched keys")
	}
	cp := Compare(mutSelf.Vc, other.Vc)
	// if other is newer
	if cp == -1 || (cp == 2 && Privilege(other.Vc, mutSelf.Vc)) {
		mutSelf.Value = other.Value
	}
	MergeIntoVC(&mutSelf.Vc, &other.Vc)
	for k, vc := range other.Deps {
		vc2, ok := mutSelf.Deps[k]
		if ok {
			MergeIntoVC(&vc2, &vc)
			mutSelf.Deps[k] = vc2
		} else {
			mutSelf.Deps[k] = vc
		}
	}
}

func MergeMeta(m1 *Meta, m2 *Meta) Meta {
	meta := Meta{}
	DeepCopy(&meta, m1)
	MergeIntoMeta(&meta, m2)
	return meta
}

func InsertOrMergeMeta(m *map[string]*Meta, k string, meta2 *Meta) {
	if meta1, ok := (*m)[k]; ok {
		MergeIntoMeta(meta1, meta2)
	} else {
		meta := Meta{}
		DeepCopy(&meta, meta2)
		(*m)[k] = &meta
	}
}
