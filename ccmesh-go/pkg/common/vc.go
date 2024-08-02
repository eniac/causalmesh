package common

type VC = [T]int

func MergeIntoVC(mutSelf, other *VC) {
	for i := 0; i < T; i++ {
		if mutSelf[i] < other[i] {
			mutSelf[i] = other[i]
		}
	}
}

func MergeVC(vc1, vc2 *VC) VC {
	vc := *vc1 // it's a copy
	MergeIntoVC(&vc, vc2)
	return vc
}

func HappensBefore(vc1, vc2 VC) bool {
	for i := 0; i < T; i++ {
		if vc1[i] > vc2[i] {
			return false
		}
	}
	if vc1 == vc2 {
		return false
	}
	return true
}

func Compare(vc1, vc2 VC) int {
	if vc1 == vc2 {
		// equal
		return 0
	}
	if HappensBefore(vc1, vc2) {
		// less
		return -1
	}
	if HappensBefore(vc2, vc1) {
		// greater
		return 1
	}
	// none
	return 2
}

func Concurrent(vc1, vc2 VC) bool {
	return Compare(vc1, vc2) == 2
}

func Privilege(vc1, vc2 VC) bool {
	if !(Concurrent(vc1, vc2)) {
		panic("vc1 and vc2 are not concurrent")
	}
	for i := 0; i < T; i++ {
		if vc1[i] == vc2[i] {
			continue
		}
		return vc1[i] > vc2[i]
	}
	panic("vc1 and vc2 are equal")
}

func InsertOrMergeVC(mutM *map[string]VC, k string, vc *VC) {
	if vc1, ok := (*mutM)[k]; ok {
		MergeIntoVC(&vc1, vc)
		(*mutM)[k] = vc1
	} else {
		(*mutM)[k] = *vc
	}
}

func VCIsEmpty(vc *VC) bool {
	for i := 0; i < T; i++ {
		if vc[i] != 0 {
			return false
		}
	}
	return true
}
