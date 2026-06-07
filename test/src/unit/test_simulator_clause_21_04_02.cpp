#include <cstdint>
#include <cstdio>
#include <fstream>
#include <string>
#include <vector>

#include "builders_ast.h"
#include "builders_systask.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

using namespace delta;
namespace {

// Writes the load data to a scratch file and returns its path.
std::string WriteTmp(const char* tag, const std::string& data) {
  std::string path = std::string("/tmp/deltahdl_test_21_04_02_") + tag + ".txt";
  std::ofstream ofs(path);
  ofs << data;
  ofs.close();
  return path;
}

// Invokes $readmemb / $readmemh on a memory named by a bare identifier.
void Readmem(SimFixture& f, const char* task, const std::string& path,
             const char* mem) {
  std::vector<Expr*> args = {MkStr(f.arena, path.c_str()), MakeId(f.arena, mem)};
  EvalExpr(MakeSysCall(f.arena, task, args), f.ctx, f.arena);
}

// Registers a fixed unpacked array `name[0 .. size-1]` of `width`-bit elements.
// `is_4state` selects the element's state-ness, which §21.4.2 keys on when it
// decides whether x/z bits read from the file survive into the memory.
void SetupMem(SimFixture& f, const char* name, int size, uint32_t width,
              bool is_4state) {
  ArrayInfo info;
  info.lo = 0;
  info.size = static_cast<uint32_t>(size);
  info.elem_width = width;
  info.is_4state = is_4state;
  f.ctx.RegisterArray(name, info);
  for (int i = 0; i < size; ++i) {
    std::string nm = std::string(name) + "[" + std::to_string(i) + "]";
    auto* s = f.arena.AllocString(nm.c_str(), nm.size());
    auto* v = f.ctx.CreateVariable(std::string_view(s, nm.size()), width);
    v->value = MakeLogic4VecVal(f.arena, width, 0);
  }
}

// Like SetupMem, but additionally tags the array's element type as an
// enumeration whose elements carry the given numeric values (see 6.19). An
// enum's default base is 2-state, so the backing elements are 2-state.
void SetupEnumMem(SimFixture& f, const char* name, int size, uint32_t width,
                  const std::vector<uint64_t>& member_values) {
  EnumTypeInfo info;
  info.type_name = "e_t";
  for (uint64_t v : member_values) info.members.push_back({"m", v});
  f.ctx.RegisterEnumType("e_t", info);
  f.ctx.SetVariableEnumType(name, "e_t");
  SetupMem(f, name, size, width, /*is_4state=*/false);
}

Variable* Cell(SimFixture& f, const char* name, int addr) {
  std::string nm = std::string(name) + "[" + std::to_string(addr) + "]";
  return f.ctx.FindVariable(nm);
}

// §21.4.2: $readmemb / $readmemh support packed 2-state data. Reading proceeds
// as for a 4-state element type, except that an x or z bit in the file is
// converted to 0 before the word is stored. A clean value loads unchanged; the
// "1x0z" word keeps only its 1 bit (binary 1000 = 8) and is fully known.
TEST(Readmem2StateTest, TwoStatePackedLoadConvertsUnknownBitsToZero) {
  SimFixture f;
  SetupMem(f, "mem", 2, 4, /*is_4state=*/false);
  std::string path = WriteTmp("twostate", "1010\n1x0z\n");

  Readmem(f, "$readmemb", path, "mem");

  EXPECT_EQ(Cell(f, "mem", 0)->value.ToUint64(), 0b1010u);
  EXPECT_EQ(Cell(f, "mem", 1)->value.ToUint64(), 0b1000u);
  EXPECT_TRUE(Cell(f, "mem", 1)->value.IsKnown());
  std::remove(path.c_str());
}

// §21.4.2 (boundary): the x/z-to-0 conversion is specific to 2-state element
// types. A 4-state element retains the unknown and high-impedance bits read
// from the file, so the same "1x0z" word is not fully known.
TEST(Readmem2StateTest, FourStateElementRetainsUnknownBits) {
  SimFixture f;
  SetupMem(f, "mem", 1, 4, /*is_4state=*/true);
  std::string path = WriteTmp("fourstate", "1x0z\n");

  Readmem(f, "$readmemb", path, "mem");

  EXPECT_FALSE(Cell(f, "mem", 0)->value.IsKnown());
  std::remove(path.c_str());
}

// §21.4.2: for an enumerated element type the file data are the numeric values
// associated with the enumeration's elements (see 6.19). In-range numbers load
// as those values without error.
TEST(Readmem2StateTest, EnumeratedTypeLoadsNumericValues) {
  SimFixture f;
  SetupEnumMem(f, "mem", 2, 2, /*member_values=*/{0, 1, 2});
  std::string path = WriteTmp("enum_ok", "0\n2\n");

  Readmem(f, "$readmemh", path, "mem");

  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(Cell(f, "mem", 0)->value.ToUint64(), 0u);
  EXPECT_EQ(Cell(f, "mem", 1)->value.ToUint64(), 2u);
  std::remove(path.c_str());
}

// §21.4.2 (shall): if a numeric value is out of range for the enumerated type,
// an error is issued and no further reading takes place. The value 5 names no
// element; the word before it loads, but reading stops there, so neither the
// offending word nor the later (in-range) value 2 reaches the memory.
TEST(Readmem2StateTest, EnumeratedValueOutOfRangeErrorsAndStopsReading) {
  SimFixture f;
  SetupEnumMem(f, "mem", 3, 3, /*member_values=*/{0, 1, 2});
  std::string path = WriteTmp("enum_oor", "1\n5\n2\n");

  Readmem(f, "$readmemh", path, "mem");

  EXPECT_TRUE(f.diag.HasErrors());
  EXPECT_EQ(Cell(f, "mem", 0)->value.ToUint64(), 1u);  // word before the error
  EXPECT_EQ(Cell(f, "mem", 1)->value.ToUint64(), 0u);  // out-of-range word dropped
  EXPECT_EQ(Cell(f, "mem", 2)->value.ToUint64(), 0u);  // later word never read
  std::remove(path.c_str());
}

// §21.4.2 (shall, edge): "out of range" for an enumerated type means the number
// matches no element, not merely that it exceeds the largest element. With a
// sparse enumeration whose elements are {0, 2}, the unused value 1 lies within
// the 0..2 span yet names no element, so it is rejected just like a value past
// the maximum. This pins the check to element membership rather than a bounds
// comparison.
TEST(Readmem2StateTest, EnumeratedSparseGapValueIsOutOfRange) {
  SimFixture f;
  SetupEnumMem(f, "mem", 1, 2, /*member_values=*/{0, 2});
  std::string path = WriteTmp("enum_gap", "1\n");

  Readmem(f, "$readmemh", path, "mem");

  EXPECT_TRUE(f.diag.HasErrors());
  EXPECT_EQ(Cell(f, "mem", 0)->value.ToUint64(), 0u);  // gap value not stored
  std::remove(path.c_str());
}

}  // namespace
