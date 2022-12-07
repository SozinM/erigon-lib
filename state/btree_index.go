package state

import (
	"bufio"
	"encoding/binary"
	"fmt"
	"math"
	"os"
	"path"
	"time"

	"github.com/google/btree"

	"github.com/ledgerwatch/erigon-lib/mmap"
)

type BtIndex struct {
	bt         *btree.BTreeG[uint64]
	mmapWin    *[mmap.MaxMapSize]byte
	mmapUnix   []byte
	data       []byte
	file       *os.File
	size       int64
	modTime    time.Time
	filePath   string
	keyCount   uint64
	baseDataID uint64
}

type page struct {
	i     uint64
	keys  uint64
	size  uint64
	nodes []*node
}

type node struct {
	key    []byte
	pos    uint64
	parent *node
}

type inode struct {
	page *page
	node *node
}

type cursor struct {
	stack []inode
}

func isEven(n uint64) bool {
	return n&1 == 0
}

type btAlloc struct {
	vx       []uint64
	vertices []uint64
	sons     [][]uint64
	d        uint64
	M        uint64
}

func logBase(n, base uint64) uint64 {
	return uint64(math.Ceil(math.Log(float64(n)) / math.Log(float64(base))))
}

func min64(a, b uint64) uint64 {
	if a < b {
		return a
	}
	return b
}
func max64(a, b uint64) uint64 {
	if a > b {
		return a
	}
	return b
}

func newBtAlloc3(k, M uint64) *btAlloc {
	var d uint64
	ks := k + 1
	d = logBase(ks, M)
	m := M >> 1

	fmt.Printf("k=%d d=%d, M=%d m=%d\n", k, d, M, m)
	a := &btAlloc{
		vx:   make([]uint64, d+1),
		sons: make([][]uint64, d+1),
		M:    M, d: d,
	}
	a.vx[0] = 1
	a.vx[d] = ks

	nnc := func(vx uint64) uint64 {
		return vx / M
	}

	for i := a.d - 1; i > 0; i-- {
		//nnc := uint64(math.Ceil(float64(a.vx[i+1]) / float64(M))+1)
		//nvc := uint64(math.Floor(float64(a.vx[i+1]) / float64(m))-1)
		//nnc := a.vx[i+1] / M
		//nvc := a.vx[i+1] / m
		bvc := a.vx[i+1] / (m + (m >> 1))
		//_, _ = nvc, nnc
		a.vx[i] = min64(uint64(math.Pow(float64(M), float64(i))), bvc)
	}

	pnv := uint64(0)
	for l := a.d - 1; l > 0; l-- {

		s := nnc(a.vx[l+1])
		lnc := uint64(0)
		left := a.vx[l+1] % M
		if pnv != 0 {
			s = nnc(pnv)
			left = pnv % M
		}
		if left > 0 {
			if left < m {
				s--
				newPrev := M - (m - left)
				dp := M - newPrev
				a.sons[l] = append(a.sons[l], 1, newPrev, 1, left+dp)
			} else {
				a.sons[l] = append(a.sons[l], 1, left)
			}
		}
		a.sons[l] = append(a.sons[l], s, M)

		for i := 0; i < len(a.sons[l]); i += 2 {
			lnc += a.sons[l][i]
		}
		pnv = lnc

		fmt.Printf("parents %d left %d\n", s, lnc)

	}
	a.sons[0] = []uint64{1, pnv}

	for i, v := range a.vx {
		fmt.Printf("L%d=%v; vx=%d \n", i, a.sons[i], v)
	}

	return a
}

func newBtAlloc2(k, M uint64) *btAlloc {
	var d uint64
	ks := k + 1
	d = logBase(ks, M)
	m := M >> 1

	fmt.Printf("k=%d d=%d, M=%d m=%d\n", k, d, M, m)
	a := &btAlloc{
		vx:   make([]uint64, d+1),
		sons: make([][]uint64, d+1),
		M:    M, d: d,
	}
	a.vx[0] = 1
	a.vx[d] = ks

	for i := a.d - 1; i > 0; i-- {
		//nnc := uint64(math.Ceil(float64(a.vx[i+1]) / float64(M))+1)
		//nvc := uint64(math.Floor(float64(a.vx[i+1]) / float64(m))-1)
		nnc := a.vx[i+1] / M
		nvc := a.vx[i+1] / m
		//bvc := a.vx[i+1] / (m + (m >> 1))
		_, _ = nvc, nnc
		a.vx[i] = min64(uint64(math.Pow(float64(M), float64(i))), nnc)
	}

	var vx uint64 //vertexTotal
	for l := uint64(0); l < uint64(a.d); l++ {
		//fmt.Printf("s' %d\n", a.vx[l+1]/a.vx[l]-1)
		s := uint64(math.Floor(float64(a.vx[l+1])/float64(a.vx[l]))) - 1
		//s := (a.vx[l+1] / a.vx[l]) - 1
		r := a.vx[l] - (a.vx[l+1] % a.vx[l])
		vx += s * r
		a.sons[l] = []uint64{r, s}
		fmt.Printf("s=%d r=%d layer_total=%d nodes=%d\n", s, r, r*s, vx)
	}
	dx := a.vx[a.d] - vx
	s := uint64(math.Floor(float64(dx)/float64(M))) - 1
	a.sons[a.d] = []uint64{s, M}
	fmt.Printf("s=%d r=%d layer_total=%d nodes=%d\n", M, s, dx, vx+dx)

	for i, v := range a.vx {
		fmt.Printf("L%d=%v; vx=%d \n", i, a.sons[i], v)
	}

	return a
}

func (a *btAlloc) walk() {
	var totalNodes uint64
	f, err := os.Create("walk.csv")
	if err != nil {
		panic(err)
	}
	fmt.Fprintf(f, "r, s\n")
	for i, s := range a.sons {
		_ = i
		if len(s) == 0 {
			continue
		}
		for j := 0; j < len(s); j += 2 {
			sc := s[j] * s[j+1]
			//totalNodes += s[j]
			for j := uint64(0); j < sc; j++ {
				totalNodes++
			}

		}
	}
	fmt.Printf("total=%d\n", totalNodes)

	var vx uint64
	for i, s := range a.sons {
		for j := 0; j < len(s); j += 2 {
			vx += s[j] * s[j+1]
		}
		fmt.Printf("w%d=%v; vx=%d \n", i, s, vx)
	}

	f.Sync()
	f.Close()
}

func OpenBtreeIndex(indexPath string) (*BtIndex, error) {
	s, err := os.Stat(indexPath)
	if err != nil {
		return nil, err
	}

	idx := &BtIndex{
		filePath: indexPath,
		size:     s.Size(),
		modTime:  s.ModTime(),
		//idx:      btree.NewG[uint64](32, commitmentItemLess),
	}

	idx.file, err = os.Open(indexPath)
	if err != nil {
		return nil, err
	}

	if idx.mmapUnix, idx.mmapWin, err = mmap.Mmap(idx.file, int(idx.size)); err != nil {
		return nil, err
	}
	idx.data = idx.mmapUnix[:idx.size]
	// Read number of keys and bytes per record
	idx.baseDataID = binary.BigEndian.Uint64(idx.data[:8])
	idx.keyCount = binary.BigEndian.Uint64(idx.data[8:16])
	return idx, nil
}

func (b *BtIndex) Size() int64 { return b.size }

func (b *BtIndex) ModTime() time.Time { return b.modTime }

func (b *BtIndex) BaseDataID() uint64 { return b.baseDataID }

func (b *BtIndex) FilePath() string { return b.filePath }

func (b *BtIndex) FileName() string { return path.Base(b.filePath) }

func (b *BtIndex) Empty() bool { return b.keyCount == 0 }

func (b *BtIndex) KeyCount() uint64 { return b.keyCount }

func (b *BtIndex) Close() error {
	if b == nil {
		return nil
	}
	if err := mmap.Munmap(b.mmapUnix, b.mmapWin); err != nil {
		return err
	}
	if err := b.file.Close(); err != nil {
		return err
	}
	return nil
}

func (b *BtIndex) Lookup(bucketHash, fingerprint uint64) uint64 {
	//TODO implement me
	panic("implement me")
}

func (b *BtIndex) OrdinalLookup(i uint64) uint64 {
	//TODO implement me
	panic("implement me")
}

func (b *BtIndex) ExtractOffsets() map[uint64]uint64 {
	//TODO implement me
	panic("implement me")
}

func (b *BtIndex) RewriteWithOffsets(w *bufio.Writer, m map[uint64]uint64) error {
	//TODO implement me
	panic("implement me")
}

func (b *BtIndex) DisableReadAhead() {
	//TODO implement me
	panic("implement me")
}

func (b *BtIndex) EnableReadAhead() *interface{} {
	//TODO implement me
	panic("implement me")
}

func (b *BtIndex) EnableMadvNormal() *interface{} {
	//TODO implement me
	panic("implement me")
}

func (b *BtIndex) EnableWillNeed() *interface{} {
	//TODO implement me
	panic("implement me")
}
