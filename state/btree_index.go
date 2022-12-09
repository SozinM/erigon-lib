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
	val    uint64
	parent uint64
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
	vx   []uint64
	bros []uint64
	pos  []int
	pl   uint64
	sons [][]uint64
	d    uint64
	M    uint64
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

func newBtAlloc(k, M uint64) *btAlloc {
	var d uint64
	ks := k + 1
	d = logBase(ks, M)
	m := M >> 1

	fmt.Printf("k=%d d=%d, M=%d m=%d\n", k, d, M, m)
	a := &btAlloc{
		vx:   make([]uint64, d+1),
		sons: make([][]uint64, d+1),
		bros: make([]uint64, d),
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

	for i, v := range a.sons {
		fmt.Printf("L%d=%v\n", i, v)
	}

	return a
}

func (a *btAlloc) init() {
	a.bros = make([]uint64, a.d)
	a.pos = make([]int, a.d)
	a.pl = a.d - 1
	for i := 0; i < int(a.d); i++ {
		a.bros[i] = a.sons[i][1]
		a.pos[i] = 1
	}
}

//wip
func (a *btAlloc) pick() uint64 {
	for {
		if a.bros[a.pl] == 0 {
			a.pos[a.pl] += 2
			if len(a.sons[a.pl]) > a.pos[a.pl] {
				a.pos[a.pl] = -1 // кончились ноды на уровне
				continue
			}
			a.bros[a.pl] = a.sons[a.pl][a.pos[a.pl]]
			a.pl--
			return 1
			//break
		}

		b := a.bros[a.pl]
		a.bros[a.pl] = 0
		return b
	}
	return 0
}

func (a *btAlloc) walkFillorder() {
	stack := make([]string, 0)
	var sp uint64
	p := -1  // parent ptr
	bl := -1 // bros left

	for l := len(a.sons) - 2; l >= 0; {
		for i := 0; i < len(a.sons[l]); i += 2 {
			nodes, ccount := a.sons[l][i], a.sons[l][i+1]
			for n := uint64(0); n < nodes; n++ {
				for j := uint64(0); j < ccount; j++ {
					stack = append(stack, fmt.Sprintf("L%d x%2d", l, sp))
					fmt.Printf("%s\n", stack[sp])
					sp++
				}
				stack = append(stack, fmt.Sprintf("L%d c%2d x%2d", l-1, ccount, sp))
				fmt.Printf("%s\n", stack[sp])
				sp++

				if l == 0 {
					continue
				}
				if p < 0 && bl < 0 {
					p = 0 // even root should have this item
					bros := a.sons[l-1][p+1]
					bl = int(bros)
				}
				bl--
				// ненадежный отсчет оставшихся братишек
				if bl != int(a.sons[l-1][p+1])-1 && bl > 0 {
					continue // skip previously marked parent
				}
				if bl <= 0 {
					p += 2
					if p >= len(a.sons[l-1]) {
						break
					}
					bros := a.sons[l-1][p+1]
					bl = int(bros)
				}
				stack = append(stack, fmt.Sprintf("L%d p%2d x%2d", l-1, p, sp))
				fmt.Printf("%s\n", stack[sp])
				sp++

			}
		}
		l -= 2 // parent row already filled by row below
	}

	//for _, s := range stack {
	//	fmt.Printf("%s\n", s)
	//}
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
