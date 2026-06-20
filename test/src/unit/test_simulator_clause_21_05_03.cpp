#include <cstdio>
#include <fstream>
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

// §21.5.3 (shall not): dumping a plain unpacked array writes a bare sequence of
// words with no @-address specifiers, so a sequential $readmem reloads it.
TEST(WritememAddressTest, UnpackedArrayWritesNoAddressSpecifiers) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_test_21_05_03_unpacked.txt";
  SetupMem(f, "mem", 0, 3, 8);
  Cell(f, "mem", 0)->value = MakeLogic4VecVal(f.arena, 8, 0x11);
  Cell(f, "mem", 1)->value = MakeLogic4VecVal(f.arena, 8, 0x22);
  Cell(f, "mem", 2)->value = MakeLogic4VecVal(f.arena, 8, 0x33);

  Writemem(f, "$writememh", path, "mem");

  std::string contents = ReadFile(path);
  EXPECT_EQ(contents, "11\n22\n33\n");
  EXPECT_EQ(contents.find('@'), std::string::npos);
  std::remove(path.c_str());
}

// §21.5.3 (shall not): a dynamic array is likewise dumped without @-address
// specifiers — the same bare sequential form as a fixed unpacked array.
TEST(WritememAddressTest, DynamicArrayWritesNoAddressSpecifiers) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_test_21_05_03_dynamic.txt";
  auto* q = f.ctx.CreateQueue("dyn", 8);
  q->elements.push_back(MakeLogic4VecVal(f.arena, 8, 0xAB));
  q->elements.push_back(MakeLogic4VecVal(f.arena, 8, 0xCD));
  ArrayInfo info;
  info.is_dynamic = true;
  info.elem_width = 8;
  f.ctx.RegisterArray("dyn", info);

  Writemem(f, "$writememh", path, "dyn");

  std::string contents = ReadFile(path);
  EXPECT_EQ(contents, "ab\ncd\n");
  EXPECT_EQ(contents.find('@'), std::string::npos);
  std::remove(path.c_str());
}

// §21.5.3 (shall): an associative array is dumped with an @-address ahead of
// every entry, since its keys are sparse and a plain sequential read could not
// place each word. The keys are written in ascending order as hexadecimal.
TEST(WritememAddressTest, AssociativeArrayWritesAddressSpecifiers) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_test_21_05_03_assoc.txt";
  auto* aa = f.ctx.CreateAssocArray("am", /*elem_width=*/8,
                                    /*is_string_key=*/false);
  aa->int_data[5] = MakeLogic4VecVal(f.arena, 8, 0xAB);
  aa->int_data[16] = MakeLogic4VecVal(f.arena, 8, 0xCD);

  Writemem(f, "$writememh", path, "am");

  std::string contents = ReadFile(path);
  // Key 16 prints as hexadecimal "10"; ascending key order is preserved.
  EXPECT_EQ(contents, "@5\nab\n@10\ncd\n");
  std::remove(path.c_str());
}

}  // namespace
