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

// Registers a fixed unpacked array `name[lo .. lo+size-1]` of `width`-bit
// elements, each backed by a zero-initialized element variable (the convention
// the simulator uses), so $writemem has a memory to dump.
void SetupMem(SimFixture& f, const char* name, int lo, int size,
              uint32_t width) {
  f.ctx.RegisterArray(name, {static_cast<uint32_t>(lo),
                             static_cast<uint32_t>(size), width, false, false,
                             false});
  for (int i = 0; i < size; ++i) {
    std::string nm = std::string(name) + "[" + std::to_string(lo + i) + "]";
    auto* s = f.arena.AllocString(nm.c_str(), nm.size());
    auto* v = f.ctx.CreateVariable(std::string_view(s, nm.size()), width);
    v->value = MakeLogic4VecVal(f.arena, width, 0);
  }
}

Variable* Cell(SimFixture& f, const char* name, int addr) {
  std::string nm = std::string(name) + "[" + std::to_string(addr) + "]";
  return f.ctx.FindVariable(nm);
}

void Writemem(SimFixture& f, const char* task, const std::string& path,
              const char* mem) {
  EvalExpr(MakeSysCall(f.arena, task,
                       {MkStr(f.arena, path.c_str()), MakeId(f.arena, mem)}),
           f.ctx, f.arena);
}

std::string ReadFile(const std::string& path) {
  std::ifstream ifs(path);
  return std::string((std::istreambuf_iterator<char>(ifs)),
                     std::istreambuf_iterator<char>());
}

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
