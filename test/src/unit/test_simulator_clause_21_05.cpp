#include <algorithm>
#include <cstdio>
#include <fstream>
#include <string>
#include <vector>

#include "builders_ast.h"
#include "builders_systask.h"
#include "fixture_simulator.h"
#include "helpers_memload.h"
#include "helpers_parser_verify.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

using namespace delta;
namespace {

// §21.5: a single (scalar) word is dumped in hexadecimal by $writememh.
TEST(IoSystemTaskTest, WritememhBasic) {
  SimFixture f;
  std::string tmp_path = "/tmp/deltahdl_test_writememh.txt";

  auto* var = f.ctx.CreateVariable("wmem", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 0xFF);

  auto* expr =
      MakeSysCall(f.arena, "$writememh",
                  {MkStr(f.arena, tmp_path.c_str()), MakeId(f.arena, "wmem")});
  EvalExpr(expr, f.ctx, f.arena);

  std::string contents = ReadFile(tmp_path);
  EXPECT_FALSE(contents.empty());
  EXPECT_NE(contents.find("ff"), std::string::npos);

  std::remove(tmp_path.c_str());
}

// §21.5: $writememb dumps the same word in binary.
TEST(IoSystemTaskTest, WritemembBasic) {
  SimFixture f;
  std::string tmp_path = "/tmp/deltahdl_test_writememb.txt";

  auto* var = f.ctx.CreateVariable("wbmem", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 0b10101010);

  auto* expr =
      MakeSysCall(f.arena, "$writememb",
                  {MkStr(f.arena, tmp_path.c_str()), MakeId(f.arena, "wbmem")});
  EvalExpr(expr, f.ctx, f.arena);

  std::string contents = ReadFile(tmp_path);
  EXPECT_FALSE(contents.empty());
  EXPECT_NE(contents.find("10101010"), std::string::npos);

  std::remove(tmp_path.c_str());
}

// §21.5: the file $writememh produces is readable by $readmemh. Dumping a
// memory array and reading it back into a fresh array reproduces every word.
TEST(IoSystemTaskTest, WritememhArrayRoundTripsThroughReadmemh) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_test_21_05_rt_h.txt";
  SetupMem(f, "src", 0, 4, 8);
  Cell(f, "src", 0)->value = MakeLogic4VecVal(f.arena, 8, 0x12);
  Cell(f, "src", 1)->value = MakeLogic4VecVal(f.arena, 8, 0x34);
  Cell(f, "src", 2)->value = MakeLogic4VecVal(f.arena, 8, 0x56);
  Cell(f, "src", 3)->value = MakeLogic4VecVal(f.arena, 8, 0x78);

  Writemem(f, "$writememh", path, "src");

  SetupMem(f, "dst", 0, 4, 8);
  Readmem(f, "$readmemh", path, "dst");

  EXPECT_EQ(Cell(f, "dst", 0)->value.ToUint64(), 0x12u);
  EXPECT_EQ(Cell(f, "dst", 1)->value.ToUint64(), 0x34u);
  EXPECT_EQ(Cell(f, "dst", 2)->value.ToUint64(), 0x56u);
  EXPECT_EQ(Cell(f, "dst", 3)->value.ToUint64(), 0x78u);
  std::remove(path.c_str());
}

// §21.5: the binary form likewise round-trips through $readmemb.
TEST(IoSystemTaskTest, WritemembArrayRoundTripsThroughReadmemb) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_test_21_05_rt_b.txt";
  SetupMem(f, "src", 0, 3, 8);
  Cell(f, "src", 0)->value = MakeLogic4VecVal(f.arena, 8, 0b00000001);
  Cell(f, "src", 1)->value = MakeLogic4VecVal(f.arena, 8, 0b10110010);
  Cell(f, "src", 2)->value = MakeLogic4VecVal(f.arena, 8, 0b11111111);

  Writemem(f, "$writememb", path, "src");

  SetupMem(f, "dst", 0, 3, 8);
  Readmem(f, "$readmemb", path, "dst");

  EXPECT_EQ(Cell(f, "dst", 0)->value.ToUint64(), 0b00000001u);
  EXPECT_EQ(Cell(f, "dst", 1)->value.ToUint64(), 0b10110010u);
  EXPECT_EQ(Cell(f, "dst", 2)->value.ToUint64(), 0b11111111u);
  std::remove(path.c_str());
}

// §21.5: when the file already exists it is overwritten, not appended to. A
// second dump of a shorter memory leaves only the new contents behind.
TEST(IoSystemTaskTest, OverwritesExistingFileWithoutAppending) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_test_21_05_overwrite.txt";
  SetupMem(f, "big", 0, 4, 8);
  Cell(f, "big", 0)->value = MakeLogic4VecVal(f.arena, 8, 0xAA);
  Cell(f, "big", 1)->value = MakeLogic4VecVal(f.arena, 8, 0xBB);
  Cell(f, "big", 2)->value = MakeLogic4VecVal(f.arena, 8, 0xCC);
  Cell(f, "big", 3)->value = MakeLogic4VecVal(f.arena, 8, 0xDD);
  Writemem(f, "$writememh", path, "big");

  SetupMem(f, "small", 0, 1, 8);
  Cell(f, "small", 0)->value = MakeLogic4VecVal(f.arena, 8, 0x11);
  Writemem(f, "$writememh", path, "small");

  std::string contents = ReadFile(path);
  // The second, shorter dump replaced the file: only its single word remains
  // and none of the first dump's words survive.
  EXPECT_NE(contents.find("11"), std::string::npos);
  EXPECT_EQ(contents.find("aa"), std::string::npos);
  EXPECT_EQ(contents.find("dd"), std::string::npos);
  EXPECT_EQ(std::count(contents.begin(), contents.end(), '\n'), 1);
  std::remove(path.c_str());
}

// §21.5: the optional start_addr / finish_addr bound the words written, and a
// finish below the start dumps them in descending address order.
TEST(IoSystemTaskTest, StartFinishBoundsAndOrdersTheDump) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_test_21_05_range.txt";
  SetupMem(f, "src", 0, 5, 8);
  for (int i = 0; i < 5; ++i) {
    Cell(f, "src", i)->value =
        MakeLogic4VecVal(f.arena, 8, 0x10 + static_cast<uint64_t>(i));
  }

  // Write addresses 3 down to 1: words 0x13, 0x12, 0x11 in that order.
  Writemem(f, "$writememh", path, "src",
           {MakeInt(f.arena, 3), MakeInt(f.arena, 1)});

  std::string contents = ReadFile(path);
  EXPECT_EQ(contents, "13\n12\n11\n");
  std::remove(path.c_str());
}

// §21.5 (Syntax 21-13): the production nests the optional arguments so that
// start_addr may appear without finish_addr. In that three-argument form the
// dump begins at start_addr and runs to the end of the memory, because the
// task defaults the missing finish bound to the array's highest address.
TEST(IoSystemTaskTest, StartAddressWithoutFinishDumpsThroughEndOfMemory) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_test_21_05_start_only.txt";
  SetupMem(f, "src", 0, 4, 8);
  Cell(f, "src", 0)->value = MakeLogic4VecVal(f.arena, 8, 0x20);
  Cell(f, "src", 1)->value = MakeLogic4VecVal(f.arena, 8, 0x21);
  Cell(f, "src", 2)->value = MakeLogic4VecVal(f.arena, 8, 0x22);
  Cell(f, "src", 3)->value = MakeLogic4VecVal(f.arena, 8, 0x23);

  // Start at address 2 with no finish supplied: words at 2 and 3 are written,
  // in ascending order, through the last element of the array.
  Writemem(f, "$writememh", path, "src", {MakeInt(f.arena, 2)});

  std::string contents = ReadFile(path);
  EXPECT_EQ(contents, "22\n23\n");
  std::remove(path.c_str());
}

}  // namespace
