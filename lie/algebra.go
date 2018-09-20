package lie

// Algebra contains type-specific Lie algebra operations.
type Algebra interface {
	DualCoxeter() int
	PositiveRoots() []Root
	KillingForm(Weight, Weight) float64
	IntKillingForm(Weight, Weight) int
	KillingFactor() int
	NewWeight() Weight
	Weights(int) []Weight
	Rho() Weight
	Level(Weight) int
	dual(Weight, Weight)
	reflectToChamber(Weight, Weight) int
	reflectEpcToChamber(epCoord) int
	nextOrbitEpc(epCoord) bool
	convertWeightToEpc(Weight, epCoord)
	newEpc(Weight) epCoord
	convertEpCoord(epCoord, Weight)
	convertRoot(Root, Weight)
}

// TypeA represents the Lie algebra of type A with the specified rank.
type TypeA struct {
	rank int
}

// DualCoxeter computes the dual Coxeter number of the Lie algebra.
func (alg TypeA) DualCoxeter() int {
	return alg.rank + 1
}

// PositiveRoots builds a list of all positive roots of the Lie algebra.
func (alg TypeA) PositiveRoots() []Root {
	retList := make([]Root, 0, alg.rank*(alg.rank+1)/2)
	root := make([]int, alg.rank)

	for i := range root {
		for j := i; j < len(root); j++ {
			root[j] = 1

			var next Root = make([]int, alg.rank)
			copy(next, root)
			retList = append(retList, next)
		}

		for j := i; j < len(root); j++ {
			root[j] = 0
		}
	}

	return retList
}

// KillingForm computes the Killing product of the given weights.
func (alg TypeA) KillingForm(wt1, wt2 Weight) float64 {
	return float64(alg.IntKillingForm(wt1, wt2)) / float64(alg.KillingFactor())
}

// IntKillingForm calculates the Killing product normalized so that the product of integral weights is an integer.
func (alg TypeA) IntKillingForm(wt1, wt2 Weight) int {
	var part1, part2, product, sum1, sum2 int

	for i := len(wt1) - 1; i >= 0; i-- {
		part1 += wt1[i]
		part2 += wt2[i]
		product += part1 * part2
		sum1 += part1
		sum2 += part2
	}

	return (alg.rank+1)*product - sum1*sum2
}

// KillingFactor returns IntKillingForm/KillingForm.
func (alg TypeA) KillingFactor() int {
	return alg.rank + 1
}

// NewWeight creates a new zero weight.
func (alg TypeA) NewWeight() Weight {
	return make([]int, alg.rank, alg.rank+1)
}

// Weights returns a slice of all weights with level at most the given int.
func (alg TypeA) Weights(level int) []Weight {
	var weightsHelper func(rank int) []Weight
	weightsHelper = func(rank int) []Weight {
		retList := make([]Weight, 0)
		if rank == 1 {
			for i := 0; i <= level; i++ {
				retList = append(retList, Weight{i})
			}
		} else {
			rMinusOneList := weightsHelper(rank - 1)
			for _, wt := range rMinusOneList {
				wtLevel := 0
				for _, coord := range wt {
					wtLevel += coord
				}
				for i := 0; i <= level-wtLevel; i++ {
					newWt := make([]int, len(wt)+1)
					copy(newWt, wt)
					newWt[len(wt)] = i
					retList = append(retList, newWt)
				}
			}
		}

		return retList
	}

	return weightsHelper(alg.rank)
}

// Rho returns one-half the sum of the positive roots of the algebra.
func (alg TypeA) Rho() Weight {
	rho := alg.NewWeight()
	for i := 0; i < alg.rank; i++ {
		rho[i] = 1
	}

	return rho
}

// Level computes the 'level' of the given weight, i.e. its product with the highest root.
func (alg TypeA) Level(wt Weight) (lv int) {
	for i := range wt {
		lv += wt[i]
	}
	return
}

// Dual computes the highest weight of the dual repr. of corresponding to the given weight.
func (alg TypeA) dual(wt Weight, rslt Weight) {
	for i := range wt {
		rslt[len(wt)-i-1] = wt[i]
	}
}

// ReflectToChamber reflects the given weight into the dominant chamber and returns
// the result with reflection parity.
func (alg TypeA) reflectToChamber(wt Weight, rslt Weight) int {
	convert := func(wt []int) epCoord { return wt }
	var epc []int
	if cap(rslt) > len(rslt) {
		epc = append(convert(rslt), 0)
		alg.convertWeightToEpc(wt, epc)
	} else {
		epc = make([]int, alg.rank+1)
		alg.convertWeightToEpc(wt, epc)
	}
	parity := alg.reflectEpcToChamber(epc)

	lastCoord := epc[len(epc)-1]
	for i := range epc {
		epc[i] = epc[i] - lastCoord
	}

	alg.convertEpCoord(epc, rslt)
	return parity
}

func (alg TypeA) reflectEpcToChamber(epc epCoord) (parity int) {
	parity = 1

	for i := range epc {
		for j := i; j > 0 && epc[j-1] < epc[j]; j-- {
			epc[j-1], epc[j] = epc[j], epc[j-1]
			parity *= -1
		}
	}
	return
}

func (alg TypeA) nextOrbitEpc(epc epCoord) bool {
	// Find first swap elt
	i := 1
	done := true
	for ; i < len(epc); i++ {
		if epc[i-1] > epc[i] {
			done = false
			break
		}
	}
	if done {
		return done
	}

	// Find second swap elt
	j := 0
	for ; j < i; j++ {
		if epc[j] > epc[i] {
			break
		}
	}

	// Swap
	epc[i], epc[j] = epc[j], epc[i]

	// Reverse elts 0...i-1
	for k := 0; k < i/2; k++ {
		epc[k], epc[i-k-1] = epc[i-k-1], epc[k]
	}

	return done
}

func (alg TypeA) newEpc(wt Weight) epCoord {
	epc := make([]int, len(wt)+1)
	alg.convertWeightToEpc(wt, epc)
	return epc
}

func (alg TypeA) convertWeightToEpc(wt Weight, epc epCoord) {
	var part int
	for i := len(wt) - 1; i >= 0; i-- {
		part += wt[i]
		epc[i] = part
	}
	epc[len(epc)-1] = 0
}

func (alg TypeA) convertEpCoord(epc epCoord, retVal Weight) {
	part := epc[len(epc)-1]
	for i := len(epc) - 2; i >= 0; i-- {
		temp := epc[i]
		retVal[i] = epc[i] - part
		part = temp
	}
}

// ConvertRoot converts a root into a weight.
func (alg TypeA) convertRoot(rt Root, rslt Weight) {
	if alg.rank == 1 {
		rslt[0] = 2 * rt[0]
		return
	}

	rslt[0] = 2*rt[0] - rt[1]
	for i := 1; i < len(rt)-1; i++ {
		rslt[i] = 2*rt[i] - rt[i+1] - rt[i-1]
	}

	rslt[len(rt)-1] = 2*rt[len(rt)-1] - rt[len(rt)-2]
}

// Root represents a root in the root lattice.
type Root []int

// Weight represents a weight.
type Weight []int

// AddWeights adds the given weights and stores the result in the reciever.
func (rslt Weight) AddWeights(wt1, wt2 Weight) {
	for i := range wt1 {
		rslt[i] = wt1[i] + wt2[i]
	}
}

// SubWeights subtracts the given weights and stores the result in the reciever.
func (rslt Weight) SubWeights(wt1, wt2 Weight) {
	for i := range wt1 {
		rslt[i] = wt1[i] - wt2[i]
	}
}

type epCoord []int

func (rslt epCoord) addEpc(wt1, wt2 []int) {
	for i := range wt1 {
		rslt[i] = wt1[i] + wt2[i]
	}
}

func (rslt epCoord) subEpc(wt1, wt2 []int) {
	for i := range wt1 {
		rslt[i] = wt1[i] - wt2[i]
	}
}
