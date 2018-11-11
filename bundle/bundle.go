package bundle

import (
	"math/big"

	"github.com/mjschust/cblocks/lie"
)

// CBBundle represents a conformal blocks bundle.
type CBBundle interface {
	Algebra() lie.Algebra
	Weights() []lie.Weight
	Level() int
	Points() int
	Rank() *big.Int
	IntersectFCurve([]int, []int, []int, []int) *big.Int
}

// SymCBBundle represents a symmetric conformal blocks bundle.
type SymCBBundle interface {
	CBBundle
	SymmetrizedDivisor() []*big.Rat
}

// NewCBBundle creates a new CBBundle.
func NewCBBundle(alg lie.Algebra, wts []lie.Weight, ell int) CBBundle {
	n := len(wts)
	newWts := make([]lie.Weight, n)
	for i := 0; i < n; i++ {
		wtCopy := alg.NewWeight()
		copy(wtCopy, wts[i])
		newWts[i] = wtCopy
	}
	return cbbundleImpl{alg, newWts, ell}
}

// NewSymmetricCBBundle creates a CBBundle with the given weight repeated n times.
func NewSymmetricCBBundle(alg lie.Algebra, wt lie.Weight, ell int, n int) SymCBBundle {
	wts := make([]lie.Weight, n)
	wtCopy := alg.NewWeight()
	copy(wtCopy, wt)
	for i := 0; i < n; i++ {
		wts[i] = wt
	}
	return symCbbundleImpl{cbbundleImpl{alg, wts, ell}}
}

type cbbundleImpl struct {
	alg lie.Algebra
	wts []lie.Weight
	ell int
}

func (bun cbbundleImpl) Algebra() lie.Algebra {
	return bun.alg
}

func (bun cbbundleImpl) Weights() []lie.Weight {
	wts := bun.wts
	n := len(wts)
	newWts := make([]lie.Weight, n)
	for i := 0; i < n; i++ {
		wtCopy := bun.alg.NewWeight()
		copy(wtCopy, wts[i])
		newWts[i] = wtCopy
	}
	return newWts
}

func (bun cbbundleImpl) Level() int {
	return bun.ell
}

func (bun cbbundleImpl) Points() int {
	return len(bun.wts)
}

func (bun cbbundleImpl) Rank() *big.Int {
	alg := bun.alg
	wts := bun.wts
	ell := bun.ell
	product := alg.Fusion(ell, wts[1:len(wts)]...)

	return product.Multiplicity(alg.Dual(wts[0]))
}

func (bun cbbundleImpl) IntersectFCurve(part1, part2, part3, part4 []int) *big.Int {
	alg := bun.alg
	ell := bun.ell
	retVal := big.NewInt(0)
	rslt := big.NewInt(0)
	wtList1 := bun.weightSubList(part1)
	wtList2 := bun.weightSubList(part2)
	wtList3 := bun.weightSubList(part3)
	wtList4 := bun.weightSubList(part4)

	prod1 := alg.Fusion(ell, wtList1...)
	prod2 := alg.Fusion(ell, wtList2...)
	prod3 := alg.Fusion(ell, wtList3...)
	prod4 := alg.Fusion(ell, wtList4...)

	zero := big.NewInt(0)
	for _, wt1 := range prod1.Weights() {
		mult1 := prod1.Multiplicity(wt1)
		if mult1.Cmp(zero) == 0 {
			continue
		}
		for _, wt2 := range prod2.Weights() {
			mult2 := prod2.Multiplicity(wt2)
			if mult2.Cmp(zero) == 0 {
				continue
			}
			for _, wt3 := range prod3.Weights() {
				mult3 := prod3.Multiplicity(wt3)
				if mult3.Cmp(zero) == 0 {
					continue
				}
				for _, wt4 := range prod4.Weights() {
					mult4 := prod4.Multiplicity(wt4)
					if mult4.Cmp(zero) == 0 {
						continue
					}
					rslt.Set(bun.degree(wt1, wt2, wt3, wt4))
					rslt.Mul(rslt, mult1)
					rslt.Mul(rslt, mult2)
					rslt.Mul(rslt, mult3)
					rslt.Mul(rslt, mult4)
					retVal.Add(retVal, rslt)
				}
			}
		}
	}

	return retVal
}

func (bun cbbundleImpl) weightSubList(part []int) []lie.Weight {
	wtList := make([]lie.Weight, len(part))
	for i, wtIndex := range part {
		wtList[i] = bun.wts[wtIndex-1]
	}
	return wtList
}

// degree computes the degree of the 4-point bundle determined by the given weights and this
// bundle's level. This calculation is essentially a normalized divisor calculation
func (bun cbbundleImpl) degree(wt1, wt2, wt3, wt4 lie.Weight) *big.Int {
	alg := bun.alg
	ell := bun.ell
	rslt := big.NewInt(0)
	retVal := big.NewInt(0)
	zero := big.NewInt(0)

	// Compute sum of casimir scalars
	bun.casimirScalar(wt1, rslt)
	retVal.Add(retVal, rslt)
	bun.casimirScalar(wt2, rslt)
	retVal.Add(retVal, rslt)
	bun.casimirScalar(wt3, rslt)
	retVal.Add(retVal, rslt)
	bun.casimirScalar(wt4, rslt)
	retVal.Add(retVal, rslt)

	// Multiply by rank of bundle
	product := alg.Fusion(ell, wt2, wt3, wt4)
	rk := product.Multiplicity(alg.Dual(wt1))
	if rk.Cmp(zero) == 0 {
		return zero
	}
	retVal.Mul(retVal, rk)

	// Subtract weighted factorizations
	poly1 := alg.Fusion(ell, wt1, wt2)
	poly2 := alg.Fusion(ell, wt3, wt4)
	retVal.Sub(retVal, bun.weightedFactor(poly1, poly2))
	poly1 = alg.Fusion(ell, wt1, wt3)
	poly2 = alg.Fusion(ell, wt2, wt4)
	retVal.Sub(retVal, bun.weightedFactor(poly1, poly2))
	poly1 = alg.Fusion(ell, wt1, wt4)
	poly2 = alg.Fusion(ell, wt2, wt3)
	retVal.Sub(retVal, bun.weightedFactor(poly1, poly2))

	// Divide by divisor factor
	denom := bun.divisorDenom()
	a := big.NewRat(0, 1)
	a.SetInt(retVal)
	a.Quo(a, denom)
	retVal.Set(a.Num())

	return retVal
}

type symCbbundleImpl struct {
	cbbundleImpl
}

func (bun symCbbundleImpl) SymmetrizedDivisor() []*big.Rat {
	alg := bun.alg
	wts := make([]lie.WeightPoly, len(bun.wts))
	for i := range bun.wts {
		wts[i] = bun.wts[i]
	}
	n := len(bun.wts)
	prod := alg.FusionProduct(bun.ell)

	// Calculate the rank and fusion products used in calculation
	poly := wts[0]
	prodSlc := make([]lie.WeightPoly, n)
	for i := 0; i < n-2; i++ {
		poly = prod.Apply(poly, wts[0])
		prodSlc[i+2] = poly
	}
	rk := prodSlc[n-1].Multiplicity(alg.Dual(bun.wts[0]))

	// Calculate the starting point of each coord
	rslt := big.NewInt(0)
	bun.casimirScalar(wts[0].(lie.Weight), rslt)
	rslt.Mul(rslt, rk)
	denom := big.NewInt(int64(n - 1))
	baseSummand := big.NewRat(0, 1)
	baseSummand.SetFrac(rslt, denom)

	// Prepare the common denominator for the coords
	sumDenom := bun.divisorDenom()

	// Compute the output vector
	a := big.NewRat(0, 1)
	retVec := make([]*big.Rat, n/2-1)
	for i := 2; i < n/2+1; i++ {
		// Compute positive summand
		summand := big.NewRat(0, 1)
		summand.Set(baseSummand)
		a.SetFrac64(int64(i*(n-i)), 1)
		summand.Mul(summand, a)

		// Compute "weighted" factorization calculation
		poly1 := prodSlc[i]
		poly2 := prodSlc[n-i]
		wfSum := bun.weightedFactor(poly1, poly2)
		a.SetInt(wfSum)

		summand.Sub(summand, a)
		summand.Quo(summand, sumDenom)
		retVec[i-2] = summand
	}

	return retVec
}

// weightedFactor Computes the rank factorization of the given weight polynomials weighted
// by casimir scalars
func (bun cbbundleImpl) weightedFactor(poly1, poly2 lie.WeightPoly) *big.Int {
	alg := bun.alg
	wfSum := big.NewInt(0)
	rslt := big.NewInt(0)
	for _, mustar := range poly1.Weights() {
		mu := alg.Dual(mustar)
		bun.casimirScalar(mu, rslt)
		rslt.Mul(rslt, poly1.Multiplicity(mustar))
		rslt.Mul(rslt, poly2.Multiplicity(mu))
		wfSum.Add(wfSum, rslt)
	}

	return wfSum
}

// divisorDenom returns the denominator of Fakhruddin's divisor formula, multiplied
// by the killing factor.
func (bun cbbundleImpl) divisorDenom() *big.Rat {
	alg := bun.alg
	divDenom := big.NewRat(0, 1)
	divDenom.SetInt(big.NewInt(int64(2 * (bun.ell + alg.DualCoxeter()) * alg.KillingFactor())))

	return divDenom
}

// Computes the casimir scalar of the given weight, scaled by the killing form
// factor.
func (bun cbbundleImpl) casimirScalar(wt lie.Weight, rslt *big.Int) {
	rho := bun.alg.Rho()
	rslt.SetInt64(int64(
		bun.alg.IntKillingForm(wt, wt) + 2*bun.alg.IntKillingForm(wt, rho)))
}
