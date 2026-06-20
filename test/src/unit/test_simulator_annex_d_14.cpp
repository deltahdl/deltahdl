#include <string>
#include <vector>

#include "builders_ast.h"
#include "builders_systask.h"
#include "fixture_simulator.h"
#include "helpers_memload.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

using namespace delta;
namespace {

// Builds and evaluates a $sreadmem* call:
//   task(mem, start, finish, str0, str1, ...)
void Sreadmem(SimFixture& f, const char* task, const char* mem, int start,
              int finish, std::vector<const char*> strings) {
  std::vector<Expr*> args = {MakeId(f.arena, mem),
                             MakeInt(f.arena, static_cast<uint64_t>(start)),
                             MakeInt(f.arena, static_cast<uint64_t>(finish))};
  for (const char* s : strings) args.push_back(MkStr(f.arena, s));
  EvalExpr(MakeSysCall(f.arena, task, args), f.ctx, f.arena);
}

// Annex D.14 (C2): $sreadmemh loads data into the memory from a character
// string, reading each unsized number as hexadecimal into successive words.
TEST(OptionalSreadmemSim, SreadmemhLoadsHexFromString) {
  SimFixture f;
  SetupMem(f, "mem", 0, 4, 8);

  Sreadmem(f, "$sreadmemh", "mem", 0, 3, {"0A 14 1E 28"});

  EXPECT_EQ(Cell(f, "mem", 0)->value.ToUint64(), 0x0Au);
  EXPECT_EQ(Cell(f, "mem", 1)->value.ToUint64(), 0x14u);
  EXPECT_EQ(Cell(f, "mem", 2)->value.ToUint64(), 0x1Eu);
  EXPECT_EQ(Cell(f, "mem", 3)->value.ToUint64(), 0x28u);
}

// Annex D.14 (C2): for $sreadmemb the numbers in the string are binary.
TEST(OptionalSreadmemSim, SreadmembParsesBinaryFromString) {
  SimFixture f;
  SetupMem(f, "mem", 0, 4, 8);

  Sreadmem(f, "$sreadmemb", "mem", 0, 1, {"1010 0110"});

  EXPECT_EQ(Cell(f, "mem", 0)->value.ToUint64(), 0b1010u);
  EXPECT_EQ(Cell(f, "mem", 1)->value.ToUint64(), 0b0110u);
}

// Annex D.14 (C2): the data may be split across several string arguments; the
// strings are taken together as the source of the load.
TEST(OptionalSreadmemSim, MultipleStringArgumentsAreConcatenated) {
  SimFixture f;
  SetupMem(f, "mem", 0, 4, 8);

  Sreadmem(f, "$sreadmemh", "mem", 0, 3, {"0A 14", "1E 28"});

  EXPECT_EQ(Cell(f, "mem", 0)->value.ToUint64(), 0x0Au);
  EXPECT_EQ(Cell(f, "mem", 1)->value.ToUint64(), 0x14u);
  EXPECT_EQ(Cell(f, "mem", 2)->value.ToUint64(), 0x1Eu);
  EXPECT_EQ(Cell(f, "mem", 3)->value.ToUint64(), 0x28u);
}

// Annex D.14 (C3): the start and finish addresses bound where the data is
// stored. With start=1, finish=2 the load begins at address 1 and fills only
// the two words inside the window, leaving the surrounding words unchanged.
TEST(OptionalSreadmemSim, StartFinishBoundTheStoredRange) {
  SimFixture f;
  SetupMem(f, "mem", 0, 4, 8);

  Sreadmem(f, "$sreadmemh", "mem", 1, 2, {"AA BB"});

  EXPECT_EQ(Cell(f, "mem", 0)->value.ToUint64(), 0x00u);
  EXPECT_EQ(Cell(f, "mem", 1)->value.ToUint64(), 0xAAu);
  EXPECT_EQ(Cell(f, "mem", 2)->value.ToUint64(), 0xBBu);
  EXPECT_EQ(Cell(f, "mem", 3)->value.ToUint64(), 0x00u);
}

// Annex D.14 (C3): when the start address exceeds the finish address the data
// is stored in descending order, exactly as for a $readmem load window.
TEST(OptionalSreadmemSim, StartGreaterThanFinishLoadsDescending) {
  SimFixture f;
  SetupMem(f, "mem", 0, 4, 8);

  Sreadmem(f, "$sreadmemh", "mem", 2, 0, {"01 02 03"});

  EXPECT_EQ(Cell(f, "mem", 2)->value.ToUint64(), 0x01u);
  EXPECT_EQ(Cell(f, "mem", 1)->value.ToUint64(), 0x02u);
  EXPECT_EQ(Cell(f, "mem", 0)->value.ToUint64(), 0x03u);
}

// Annex D.14 (C4): the strings take the same format as a $readmem load file, so
// an @-address embedded in the string repositions the load cursor.
TEST(OptionalSreadmemSim, AtAddressInStringRepositionsCursor) {
  SimFixture f;
  SetupMem(f, "mem", 0, 4, 8);

  Sreadmem(f, "$sreadmemh", "mem", 0, 3, {"@2 FF"});

  EXPECT_EQ(Cell(f, "mem", 0)->value.ToUint64(), 0x00u);
  EXPECT_EQ(Cell(f, "mem", 1)->value.ToUint64(), 0x00u);
  EXPECT_EQ(Cell(f, "mem", 2)->value.ToUint64(), 0xFFu);
}

// Annex D.14 (C2, edge): when the data spans several string arguments, the
// strings are kept separate rather than glued together, so two adjacent
// single-token strings load as two distinct words instead of one combined
// token. (If they were concatenated, "0A" and "14" would form the single token
// "0A14".)
TEST(OptionalSreadmemSim, AdjacentStringsAreTokenSeparated) {
  SimFixture f;
  SetupMem(f, "mem", 0, 4, 8);

  Sreadmem(f, "$sreadmemh", "mem", 0, 1, {"0A", "14"});

  EXPECT_EQ(Cell(f, "mem", 0)->value.ToUint64(), 0x0Au);
  EXPECT_EQ(Cell(f, "mem", 1)->value.ToUint64(), 0x14u);
}

// Annex D.14 (C1, error): the syntax requires at least one data string after
// the addresses. A call supplying no string has nothing to load, so the memory
// is left unchanged.
TEST(OptionalSreadmemSim, MissingDataStringLeavesMemoryUnchanged) {
  SimFixture f;
  SetupMem(f, "mem", 0, 4, 8);

  Sreadmem(f, "$sreadmemh", "mem", 0, 1, {});

  EXPECT_EQ(Cell(f, "mem", 0)->value.ToUint64(), 0x00u);
  EXPECT_EQ(Cell(f, "mem", 1)->value.ToUint64(), 0x00u);
  EXPECT_EQ(Cell(f, "mem", 2)->value.ToUint64(), 0x00u);
  EXPECT_EQ(Cell(f, "mem", 3)->value.ToUint64(), 0x00u);
}

}  // namespace
