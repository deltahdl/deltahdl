#include <cstdio>
#include <fstream>
#include <string>
#include <utility>
#include <vector>

#include "builders_ast.h"
#include "builders_systask.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

using namespace delta;
namespace {

using Dim = std::pair<int, int>;  // {low address, extent}

// Creates the zero-initialized element variable named by `nm` (a fully
// subscripted element such as "mem[1][2][6]").
void MakeCell(SimFixture& f, const std::string& nm, uint32_t width) {
  auto* s = f.arena.AllocString(nm.c_str(), nm.size());
  auto* v = f.ctx.CreateVariable(std::string_view(s, nm.size()), width);
  v->value = MakeLogic4VecVal(f.arena, width, 0);
}

// Recursively walks every combination of subscripts and creates a backing
// element variable for each, matching the nested-bracket naming the simulator
// uses for a multidimensional unpacked array (mem[i0][i1]...).
void CreateCells(SimFixture& f, const std::string& prefix,
                 const std::vector<Dim>& dims, size_t d, uint32_t width) {
  if (d == dims.size()) {
    MakeCell(f, prefix, width);
    return;
  }
  for (int i = 0; i < dims[d].second; ++i) {
    CreateCells(f, prefix + "[" + std::to_string(dims[d].first + i) + "]", dims,
                d + 1, width);
  }
}

// Registers a multidimensional unpacked array `name` whose dimensions, given
// outermost first as {low, extent} pairs, drive the §21.4.3 row-major load.
// `descending_top` marks the highest dimension's declaration as descending to
// confirm the file layout is unaffected by declaration direction.
void SetupMultiMem(SimFixture& f, const char* name, std::vector<Dim> dims,
                   uint32_t width, bool descending_top = false) {
  ArrayInfo info;
  info.elem_width = width;
  info.lo = static_cast<uint32_t>(dims.front().first);
  info.size = static_cast<uint32_t>(dims.front().second);
  info.is_descending = descending_top;
  for (const auto& d : dims) {
    info.dim_los.push_back(static_cast<uint32_t>(d.first));
    info.dim_sizes.push_back(static_cast<uint32_t>(d.second));
  }
  f.ctx.RegisterArray(name, info);
  CreateCells(f, name, dims, 0, width);
}

// Looks up an element by its list of subscripts.
Variable* MCell(SimFixture& f, const char* name, std::vector<int> idx) {
  std::string nm = name;
  for (int i : idx) nm += "[" + std::to_string(i) + "]";
  return f.ctx.FindVariable(nm);
}

std::string WriteTmp(const char* tag, const std::string& data) {
  std::string path = std::string("/tmp/deltahdl_test_21_04_03_") + tag + ".txt";
  std::ofstream ofs(path);
  ofs << data;
  ofs.close();
  return path;
}

void Readmem(SimFixture& f, const char* task, const std::string& path,
             const char* mem) {
  EvalExpr(MakeSysCall(f.arena, task,
                       {MkStr(f.arena, path.c_str()), MakeId(f.arena, mem)}),
           f.ctx, f.arena);
}

// Writes the canonical four-word hex file (11/22/33/44) under `tag`, loads it
// into a freshly set-up 2x2 "mem", and asserts the row-major fill. Shared by
// the tests that confirm the load order is independent of any per-test framing
// (e.g. ascending vs descending highest-dimension declaration).
void ExpectFourWordRowMajorFill(SimFixture& f, const char* tag) {
  std::string path = WriteTmp(tag, "11\n22\n33\n44\n");

  Readmem(f, "$readmemh", path, "mem");

  EXPECT_EQ(MCell(f, "mem", {0, 0})->value.ToUint64(), 0x11u);
  EXPECT_EQ(MCell(f, "mem", {0, 1})->value.ToUint64(), 0x22u);
  EXPECT_EQ(MCell(f, "mem", {1, 0})->value.ToUint64(), 0x33u);
  EXPECT_EQ(MCell(f, "mem", {1, 1})->value.ToUint64(), 0x44u);
  std::remove(path.c_str());
}

// §21.4.3: the file is read in row-major order, the lowest (rightmost-declared)
// dimension varying the most rapidly. A 2x2 array therefore fills [0][0],
// [0][1], [1][0], [1][1] in turn.
TEST(IoMultiDimReadmemTest, RowMajorInnermostVariesFastest) {
  SimFixture f;
  SetupMultiMem(f, "mem", {{0, 2}, {0, 2}}, 8);
  ExpectFourWordRowMajorFill(f, "rowmajor");
}

// §21.4.3: when a file without address entries contains incomplete data, the
// load stops at the last initialized word and any remaining words are left
// unchanged.
TEST(IoMultiDimReadmemTest, IncompleteFileLeavesRemainderUnchanged) {
  SimFixture f;
  SetupMultiMem(f, "mem", {{0, 2}, {0, 2}}, 8);
  std::string path = WriteTmp("incomplete", "11\n22\n33\n");  // 3 of 4 words

  Readmem(f, "$readmemh", path, "mem");

  EXPECT_EQ(MCell(f, "mem", {0, 0})->value.ToUint64(), 0x11u);
  EXPECT_EQ(MCell(f, "mem", {1, 0})->value.ToUint64(), 0x33u);
  EXPECT_EQ(MCell(f, "mem", {1, 1})->value.ToUint64(), 0x00u);  // untouched
  std::remove(path.c_str());
}

// §21.4.3: an address entry exclusively names a word of the highest dimension;
// loading resumes at the first subword enclosed by that word and fills it.
TEST(IoMultiDimReadmemTest, AddressEntryAddressesHighestDimension) {
  SimFixture f;
  SetupMultiMem(f, "mem", {{0, 3}, {0, 2}}, 8);
  std::string path = WriteTmp("addr", "@1\nAA\nBB\n");

  Readmem(f, "$readmemh", path, "mem");

  EXPECT_EQ(MCell(f, "mem", {1, 0})->value.ToUint64(), 0xAAu);
  EXPECT_EQ(MCell(f, "mem", {1, 1})->value.ToUint64(), 0xBBu);
  EXPECT_EQ(MCell(f, "mem", {0, 0})->value.ToUint64(),
            0x00u);  // word 0 untouched
  EXPECT_EQ(MCell(f, "mem", {2, 0})->value.ToUint64(),
            0x00u);  // word 2 untouched
  std::remove(path.c_str());
}

// §21.4.3: if a file with address entries holds too few words to completely
// fill the addressed highest-dimension word, the remaining subwords of that
// word are left unchanged.
TEST(IoMultiDimReadmemTest, InsufficientWordsForAddressedWordLeaveSubwords) {
  SimFixture f;
  SetupMultiMem(f, "mem", {{0, 3}, {0, 2}}, 8);
  std::string path =
      WriteTmp("addr_partial", "@2\nAA\n");  // only 1 of 2 subwords

  Readmem(f, "$readmemh", path, "mem");

  EXPECT_EQ(MCell(f, "mem", {2, 0})->value.ToUint64(), 0xAAu);
  EXPECT_EQ(MCell(f, "mem", {2, 1})->value.ToUint64(),
            0x00u);  // subword untouched
  std::remove(path.c_str());
}

// §21.4.3: the file data is hierarchical — each successive lower dimension is
// entirely enclosed by a higher dimension word. A three-dimensional array with
// a nonzero innermost low address fills with the innermost subscript varying
// fastest, then the middle, then the outermost.
TEST(IoMultiDimReadmemTest, ThreeDimensionalHierarchicalOrder) {
  SimFixture f;
  // mem[0:1][0:1][5:6]: outermost 0..1, middle 0..1, innermost 5..6.
  SetupMultiMem(f, "mem", {{0, 2}, {0, 2}, {5, 2}}, 8);
  std::string path = WriteTmp("three_d", "01\n02\n03\n04\n05\n06\n07\n08\n");

  Readmem(f, "$readmemh", path, "mem");

  EXPECT_EQ(MCell(f, "mem", {0, 0, 5})->value.ToUint64(), 0x01u);
  EXPECT_EQ(MCell(f, "mem", {0, 0, 6})->value.ToUint64(), 0x02u);
  EXPECT_EQ(MCell(f, "mem", {0, 1, 5})->value.ToUint64(), 0x03u);
  EXPECT_EQ(MCell(f, "mem", {0, 1, 6})->value.ToUint64(), 0x04u);
  EXPECT_EQ(MCell(f, "mem", {1, 0, 5})->value.ToUint64(), 0x05u);
  EXPECT_EQ(MCell(f, "mem", {1, 0, 6})->value.ToUint64(), 0x06u);
  EXPECT_EQ(MCell(f, "mem", {1, 1, 5})->value.ToUint64(), 0x07u);
  EXPECT_EQ(MCell(f, "mem", {1, 1, 6})->value.ToUint64(), 0x08u);
  std::remove(path.c_str());
}

// §21.4.3: every dimension's entries run from low to high address, so the file
// layout would be identical if a dimension's declaration were reversed
// (ascending vs descending). The loader fills low-address-first even when the
// highest dimension is declared descending.
TEST(IoMultiDimReadmemTest, DeclarationDirectionDoesNotAffectLayout) {
  SimFixture f;
  SetupMultiMem(f, "mem", {{0, 2}, {0, 2}}, 8, /*descending_top=*/true);
  // The loader still fills low-address-first ([0][0]..[1][1]) despite the
  // highest dimension being declared descending.
  ExpectFourWordRowMajorFill(f, "reversed");
}

// §21.4.3: when a multidimensional unpacked array's element spans multiple
// packed dimensions, each file word is composed of the sum total of all packed
// bits (the bit layout itself is defined in §7.4.4). A 2x2 array whose element
// is 16 bits wide (e.g. a packed [1:0][7:0]) therefore reads one full 16-bit
// word per element.
TEST(IoMultiDimReadmemTest, PackedElementComposesFullWord) {
  SimFixture f;
  SetupMultiMem(f, "mem", {{0, 2}, {0, 2}}, 16);
  std::string path = WriteTmp("packed", "DEAD\nBEEF\n0001\nF00D\n");

  Readmem(f, "$readmemh", path, "mem");

  EXPECT_EQ(MCell(f, "mem", {0, 0})->value.ToUint64(), 0xDEADu);
  EXPECT_EQ(MCell(f, "mem", {0, 1})->value.ToUint64(), 0xBEEFu);
  EXPECT_EQ(MCell(f, "mem", {1, 0})->value.ToUint64(), 0x0001u);
  EXPECT_EQ(MCell(f, "mem", {1, 1})->value.ToUint64(), 0xF00Du);
  std::remove(path.c_str());
}

// §21.4.3: both $readmemb and $readmemh work with multidimensional unpacked
// arrays. $readmemb fills the same row-major sequence, reading each word as a
// binary number.
TEST(IoMultiDimReadmemTest, ReadmembFillsMultiDimRowMajor) {
  SimFixture f;
  SetupMultiMem(f, "mem", {{0, 2}, {0, 2}}, 8);
  std::string path =
      WriteTmp("binary", "00000001\n00000010\n00000011\n00000100\n");

  Readmem(f, "$readmemb", path, "mem");

  EXPECT_EQ(MCell(f, "mem", {0, 0})->value.ToUint64(), 1u);
  EXPECT_EQ(MCell(f, "mem", {0, 1})->value.ToUint64(), 2u);
  EXPECT_EQ(MCell(f, "mem", {1, 0})->value.ToUint64(), 3u);
  EXPECT_EQ(MCell(f, "mem", {1, 1})->value.ToUint64(), 4u);
  std::remove(path.c_str());
}

// §21.4.3: since address entries name only highest-dimension words, an address
// beyond that dimension's word range cannot name a valid word; the load reports
// an error and performs no assignment.
TEST(IoMultiDimReadmemTest, AddressBeyondHighestDimensionIsError) {
  SimFixture f;
  SetupMultiMem(f, "mem", {{0, 2}, {0, 2}}, 8);  // highest dimension is 0..1
  std::string path = WriteTmp("addr_oob", "@5\nAA\n");

  Readmem(f, "$readmemh", path, "mem");

  EXPECT_TRUE(f.diag.HasErrors());
  EXPECT_EQ(MCell(f, "mem", {0, 0})->value.ToUint64(),
            0x00u);  // nothing loaded
  EXPECT_EQ(MCell(f, "mem", {1, 1})->value.ToUint64(), 0x00u);
  std::remove(path.c_str());
}

}  // namespace
