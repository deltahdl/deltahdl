#include <gtest/gtest.h>

#include <cstdint>
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

struct SreadmemCall {
  const char* task;
  const char* mem;
  int start;
  int finish;
  std::vector<const char*> strings;
};

void Sreadmem(SimFixture& f, const SreadmemCall& call) {
  std::vector<Expr*> args = {
      MakeId(f.arena, call.mem),
      MakeInt(f.arena, static_cast<uint64_t>(call.start)),
      MakeInt(f.arena, static_cast<uint64_t>(call.finish))};
  for (const char* s : call.strings) args.push_back(MkStr(f.arena, s));
  EvalExpr(MakeSysCall(f.arena, call.task, args), f.ctx, f.arena);
}

TEST(OptionalSreadmemSim, SreadmemhLoadsHexFromString) {
  SimFixture f;
  SetupMem(f, "mem", 0, 4, 8);

  Sreadmem(f, {"$sreadmemh", "mem", 0, 3, {"0A 14 1E 28"}});

  EXPECT_EQ(Cell(f, "mem", 0)->value.ToUint64(), 0x0Au);
  EXPECT_EQ(Cell(f, "mem", 1)->value.ToUint64(), 0x14u);
  EXPECT_EQ(Cell(f, "mem", 2)->value.ToUint64(), 0x1Eu);
  EXPECT_EQ(Cell(f, "mem", 3)->value.ToUint64(), 0x28u);
}

TEST(OptionalSreadmemSim, SreadmembParsesBinaryFromString) {
  SimFixture f;
  SetupMem(f, "mem", 0, 4, 8);

  Sreadmem(f, {"$sreadmemb", "mem", 0, 1, {"1010 0110"}});

  EXPECT_EQ(Cell(f, "mem", 0)->value.ToUint64(), 0b1010u);
  EXPECT_EQ(Cell(f, "mem", 1)->value.ToUint64(), 0b0110u);
}

TEST(OptionalSreadmemSim, MultipleStringArgumentsAreConcatenated) {
  SimFixture f;
  SetupMem(f, "mem", 0, 4, 8);

  Sreadmem(f, {"$sreadmemh", "mem", 0, 3, {"0A 14", "1E 28"}});

  EXPECT_EQ(Cell(f, "mem", 0)->value.ToUint64(), 0x0Au);
  EXPECT_EQ(Cell(f, "mem", 1)->value.ToUint64(), 0x14u);
  EXPECT_EQ(Cell(f, "mem", 2)->value.ToUint64(), 0x1Eu);
  EXPECT_EQ(Cell(f, "mem", 3)->value.ToUint64(), 0x28u);
}

TEST(OptionalSreadmemSim, StartFinishBoundTheStoredRange) {
  SimFixture f;
  SetupMem(f, "mem", 0, 4, 8);

  Sreadmem(f, {"$sreadmemh", "mem", 1, 2, {"AA BB"}});

  EXPECT_EQ(Cell(f, "mem", 0)->value.ToUint64(), 0x00u);
  EXPECT_EQ(Cell(f, "mem", 1)->value.ToUint64(), 0xAAu);
  EXPECT_EQ(Cell(f, "mem", 2)->value.ToUint64(), 0xBBu);
  EXPECT_EQ(Cell(f, "mem", 3)->value.ToUint64(), 0x00u);
}

TEST(OptionalSreadmemSim, StartGreaterThanFinishLoadsDescending) {
  SimFixture f;
  SetupMem(f, "mem", 0, 4, 8);

  Sreadmem(f, {"$sreadmemh", "mem", 2, 0, {"01 02 03"}});

  EXPECT_EQ(Cell(f, "mem", 2)->value.ToUint64(), 0x01u);
  EXPECT_EQ(Cell(f, "mem", 1)->value.ToUint64(), 0x02u);
  EXPECT_EQ(Cell(f, "mem", 0)->value.ToUint64(), 0x03u);
}

TEST(OptionalSreadmemSim, AtAddressInStringRepositionsCursor) {
  SimFixture f;
  SetupMem(f, "mem", 0, 4, 8);

  Sreadmem(f, {"$sreadmemh", "mem", 0, 3, {"@2 FF"}});

  EXPECT_EQ(Cell(f, "mem", 0)->value.ToUint64(), 0x00u);
  EXPECT_EQ(Cell(f, "mem", 1)->value.ToUint64(), 0x00u);
  EXPECT_EQ(Cell(f, "mem", 2)->value.ToUint64(), 0xFFu);
}

TEST(OptionalSreadmemSim, AdjacentStringsAreTokenSeparated) {
  SimFixture f;
  SetupMem(f, "mem", 0, 4, 8);

  Sreadmem(f, {"$sreadmemh", "mem", 0, 1, {"0A", "14"}});

  EXPECT_EQ(Cell(f, "mem", 0)->value.ToUint64(), 0x0Au);
  EXPECT_EQ(Cell(f, "mem", 1)->value.ToUint64(), 0x14u);
}

TEST(OptionalSreadmemSim, MissingDataStringLeavesMemoryUnchanged) {
  SimFixture f;
  SetupMem(f, "mem", 0, 4, 8);

  Sreadmem(f, {"$sreadmemh", "mem", 0, 1, {}});

  EXPECT_EQ(Cell(f, "mem", 0)->value.ToUint64(), 0x00u);
  EXPECT_EQ(Cell(f, "mem", 1)->value.ToUint64(), 0x00u);
  EXPECT_EQ(Cell(f, "mem", 2)->value.ToUint64(), 0x00u);
  EXPECT_EQ(Cell(f, "mem", 3)->value.ToUint64(), 0x00u);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "$sreadmemh takes a memory name, a start address, a finish "
                    "address, and one or more strings, and this call has fewer",
                    0, "D.14"));
}

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

TEST(OptionalSreadmemSim, AShortSreadmembCallIsReportedUnderItsOwnName) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  reg [7:0] mem [0:3];\n"
      "  initial begin\n"
      "    $sreadmemb(mem, 1);\n"
      "    $display(\"%h %h\", mem[0], mem[1]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "xx xx\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$sreadmemb takes a memory name, a start address, "
                            "a finish address, and one or more strings, and "
                            "this call has fewer",
                            4, "D.14"));
}

}  // namespace
