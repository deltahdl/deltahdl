#include <cstdio>
#include <fstream>
#include <string>
#include <vector>

#include "builders_ast.h"
#include "builders_systask.h"
#include "fixture_simulator.h"
#include "helpers_parser_verify.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

using namespace delta;
namespace {

// §21.5.1 says $writememb / $writememh treat packed data exactly as $readmemb /
// $readmemh do (see 21.4.1): each element of an unpacked array is the equivalent
// vector word, written as a single number whose width is the element's full
// packed width. For fully known words this is observed as a round-trip -- a
// memory dumped by $writemem and reloaded by the matching $readmem reproduces
// every packed word. Four-state words are observed at the file the write task
// produces, since that text is precisely the form the matching read task accepts.

// Registers an unpacked array whose elements are `width`-bit packed vectors,
// each backed by an element variable named `name[index]` (the simulator's
// convention), so the write/read tasks have a memory to operate on.
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

void Readmem(SimFixture& f, const char* task, const std::string& path,
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

// §21.5.1: a packed word wider than a single hex digit is written as one number
// the matching $readmemh reads back identically. Each 32-bit element occupies
// one line, so the multi-nibble packed value survives the round-trip whole.
TEST(IoSystemTaskTest, WidePackedWordRoundTripsThroughReadmemh) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_test_21_05_01_wide.txt";
  SetupMem(f, "src", 0, 3, 32);
  Cell(f, "src", 0)->value = MakeLogic4VecVal(f.arena, 32, 0x0000BEEFu);
  Cell(f, "src", 1)->value = MakeLogic4VecVal(f.arena, 32, 0xDEADBEEFu);
  Cell(f, "src", 2)->value = MakeLogic4VecVal(f.arena, 32, 0x12345678u);

  Writemem(f, "$writememh", path, "src");

  SetupMem(f, "dst", 0, 3, 32);
  Readmem(f, "$readmemh", path, "dst");

  EXPECT_EQ(Cell(f, "dst", 0)->value.ToUint64(), 0x0000BEEFu);
  EXPECT_EQ(Cell(f, "dst", 1)->value.ToUint64(), 0xDEADBEEFu);
  EXPECT_EQ(Cell(f, "dst", 2)->value.ToUint64(), 0x12345678u);
  std::remove(path.c_str());
}

// §21.5.1: packed data is four-state, so a word's unknown (x) and high-impedance
// (z) bits are written out -- and distinguished from each other -- in the same
// textual form $readmemb accepts. $writememb emits one four-state digit per bit,
// preserving the whole packed value rather than collapsing it to a known number.
TEST(IoSystemTaskTest, PackedFourStateBitsWrittenInReadmemForm) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_test_21_05_01_xz.txt";
  SetupMem(f, "src", 0, 1, 8);
  // Build the 8-bit word 1 0 x z 1 0 0 1. In the four-state encoding a known bit
  // has bval clear, an x bit is bval set with aval clear, and a z bit is bval
  // set with aval set; bits 5 (x) and 4 (z) carry the unknown/high-Z values.
  Logic4Vec v = MakeLogic4VecVal(f.arena, 8, 0);
  v.words[0].aval = 0b10011001u;  // the 1 bits, plus the z bit's set aval
  v.words[0].bval = 0b00110000u;  // bits 5 and 4 are the x and z positions
  Cell(f, "src", 0)->value = v;

  Writemem(f, "$writememb", path, "src");

  // The file holds the exact four-state rendering of the packed word: distinct
  // x and z characters in their bit positions, ready for $readmemb to consume.
  EXPECT_EQ(ReadFile(path), "10xz1001\n");
  std::remove(path.c_str());
}

}  // namespace
