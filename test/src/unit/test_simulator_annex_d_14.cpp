#include <string>
#include <vector>

#include "builders_ast.h"
#include "builders_systask.h"
#include "fixture_simulator.h"
#include "helpers_memload.h"
#include "helpers_reported_error.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

using namespace delta;
namespace {

// Parameters of a $sreadmem* call:
//   task(mem, start, finish, str0, str1, ...)
struct SreadmemCall {
  const char* task;
  const char* mem;
  int start;
  int finish;
  std::vector<const char*> strings;
};

// Builds and evaluates a $sreadmem* call.
void Sreadmem(SimFixture& f, const SreadmemCall& call) {
  std::vector<Expr*> args = {
      MakeId(f.arena, call.mem),
      MakeInt(f.arena, static_cast<uint64_t>(call.start)),
      MakeInt(f.arena, static_cast<uint64_t>(call.finish))};
  for (const char* s : call.strings) args.push_back(MkStr(f.arena, s));
  EvalExpr(MakeSysCall(f.arena, call.task, args), f.ctx, f.arena);
}

// Annex D.14 (C2): $sreadmemh loads data into the memory from a character
// string, reading each unsized number as hexadecimal into successive words.
TEST(OptionalSreadmemSim, SreadmemhLoadsHexFromString) {
  SimFixture f;
  SetupMem(f, "mem", 0, 4, 8);

  Sreadmem(f, {"$sreadmemh", "mem", 0, 3, {"0A 14 1E 28"}});

  EXPECT_EQ(Cell(f, "mem", 0)->value.ToUint64(), 0x0Au);
  EXPECT_EQ(Cell(f, "mem", 1)->value.ToUint64(), 0x14u);
  EXPECT_EQ(Cell(f, "mem", 2)->value.ToUint64(), 0x1Eu);
  EXPECT_EQ(Cell(f, "mem", 3)->value.ToUint64(), 0x28u);
}

// Annex D.14 (C2): for $sreadmemb the numbers in the string are binary.
TEST(OptionalSreadmemSim, SreadmembParsesBinaryFromString) {
  SimFixture f;
  SetupMem(f, "mem", 0, 4, 8);

  Sreadmem(f, {"$sreadmemb", "mem", 0, 1, {"1010 0110"}});

  EXPECT_EQ(Cell(f, "mem", 0)->value.ToUint64(), 0b1010u);
  EXPECT_EQ(Cell(f, "mem", 1)->value.ToUint64(), 0b0110u);
}

// Annex D.14 (C2): the data may be split across several string arguments; the
// strings are taken together as the source of the load.
TEST(OptionalSreadmemSim, MultipleStringArgumentsAreConcatenated) {
  SimFixture f;
  SetupMem(f, "mem", 0, 4, 8);

  Sreadmem(f, {"$sreadmemh", "mem", 0, 3, {"0A 14", "1E 28"}});

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

  Sreadmem(f, {"$sreadmemh", "mem", 1, 2, {"AA BB"}});

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

  Sreadmem(f, {"$sreadmemh", "mem", 2, 0, {"01 02 03"}});

  EXPECT_EQ(Cell(f, "mem", 2)->value.ToUint64(), 0x01u);
  EXPECT_EQ(Cell(f, "mem", 1)->value.ToUint64(), 0x02u);
  EXPECT_EQ(Cell(f, "mem", 0)->value.ToUint64(), 0x03u);
}

// Annex D.14 (C4): the strings take the same format as a $readmem load file, so
// an @-address embedded in the string repositions the load cursor.
TEST(OptionalSreadmemSim, AtAddressInStringRepositionsCursor) {
  SimFixture f;
  SetupMem(f, "mem", 0, 4, 8);

  Sreadmem(f, {"$sreadmemh", "mem", 0, 3, {"@2 FF"}});

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

  Sreadmem(f, {"$sreadmemh", "mem", 0, 1, {"0A", "14"}});

  EXPECT_EQ(Cell(f, "mem", 0)->value.ToUint64(), 0x0Au);
  EXPECT_EQ(Cell(f, "mem", 1)->value.ToUint64(), 0x14u);
}

// Annex D.14 (C1, error): the syntax requires at least one data string after
// the addresses. A call supplying no string has nothing to load, so the memory
// is left unchanged, and the call is reported; the report's place is observed
// by ACallWithoutAStringIsReportedUnderD14, which runs the call from a source.
TEST(OptionalSreadmemSim, MissingDataStringLeavesMemoryUnchanged) {
  SimFixture f;
  SetupMem(f, "mem", 0, 4, 8);

  Sreadmem(f, {"$sreadmemh", "mem", 0, 1, {}});

  EXPECT_EQ(Cell(f, "mem", 0)->value.ToUint64(), 0x00u);
  EXPECT_EQ(Cell(f, "mem", 1)->value.ToUint64(), 0x00u);
  EXPECT_EQ(Cell(f, "mem", 2)->value.ToUint64(), 0x00u);
  EXPECT_EQ(Cell(f, "mem", 3)->value.ToUint64(), 0x00u);
}

// The cases above hand the evaluator a call built by hand. The four below run
// a design, so the memory is one the module declares and the strings are the
// literals the source carries.

// Annex D.14: $sreadmemh loads the memory named by its first argument from
// the strings that follow the two addresses, reading each number as
// hexadecimal into successive words from the start address.
TEST(OptionalSreadmemSim, LoadsADeclaredMemoryFromTheSource) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  reg [7:0] mem [0:3];\n"
      "  initial begin\n"
      "    $sreadmemh(mem, 0, 3, \"0A 14 1E 28\");\n"
      "    $display(\"%h %h %h %h\", mem[0], mem[1], mem[2], mem[3]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0a 14 1e 28\n");
}

// Annex D.14: the start and finish addresses bound where the data is stored,
// so a $sreadmemb given 1 and 2 fills those two words and leaves the words
// outside the bounds as they were.
TEST(OptionalSreadmemSim, TheAddressesBoundWhereTheSourceDataIsStored) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  reg [7:0] mem [0:3];\n"
      "  initial begin\n"
      "    $sreadmemb(mem, 1, 2, \"1010 0110\");\n"
      "    $display(\"%h %h %h %h\", mem[0], mem[1], mem[2], mem[3]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "xx 0a 06 xx\n");
}

// Annex D.14: the strings take the format of a $readmem load file, so a
// comment and an @ address in a string are read as they are in a file: the
// comment loads nothing and the address places the word that follows it.
TEST(OptionalSreadmemSim, AStringCarriesACommentAndAnAddressAsAFileDoes) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  reg [7:0] mem [0:3];\n"
      "  initial begin\n"
      "    $sreadmemh(mem, 0, 3, \"// header\\n@2 7F\", \"/* skip */ 01\");\n"
      "    $display(\"%h %h %h %h\", mem[0], mem[1], mem[2], mem[3]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "xx xx 7f 01\n");
}

// Annex D.14: the syntax takes a memory name, both addresses, and at least
// one string, so a call giving no string is reported under D.14 at the call
// rather than loading nothing in silence, and the memory is left as it was.
TEST(OptionalSreadmemSim, ACallWithoutAStringIsReportedUnderD14) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  reg [7:0] mem [0:3];\n"
      "  initial begin\n"
      "    $sreadmemh(mem, 0, 3);\n"
      "    $display(\"%h %h\", mem[0], mem[3]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "xx xx\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$sreadmemh takes a memory name, a start address, "
                            "a finish address, and one or more strings, and "
                            "this call has fewer",
                            4, "D.14"));
}

}  // namespace
