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

// §21.5.2 says $writememb / $writememh can dump unpacked arrays of 2-state
// types, such as int or enumerated types. A 2-state word carries no unknown or
// high-impedance bits, so it is written as a plain number. For an enumerated
// array, the value placed in the file is the enum member's ordinal value (its
// underlying integer value per 6.19), not its position or name -- which is
// exactly the form the matching $readmem task reads back.

// §21.5.2: an unpacked array of a 2-state type (e.g. int) is dumped one word
// per line. Because a 2-state word has no x or z bits, every element is written
// as a plain hexadecimal number -- never a four-state digit.
TEST(IoSystemTaskTest, TwoStateIntegerArrayIsWritten) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_test_21_05_02_int.txt";
  SetupMem(f, "mem", 0, 3, 32, /*four_state=*/false);
  Cell(f, "mem", 0)->value = MakeLogic4VecVal(f.arena, 32, 0x0000002Au);
  Cell(f, "mem", 1)->value = MakeLogic4VecVal(f.arena, 32, 0xDEADBEEFu);
  Cell(f, "mem", 2)->value = MakeLogic4VecVal(f.arena, 32, 0x00000000u);

  Writemem(f, "$writememh", path, "mem");

  // Plain numbers only: the 2-state words print as their hexadecimal value with
  // no x/z tokens anywhere in the dump.
  EXPECT_EQ(ReadFile(path), "0000002a\ndeadbeef\n00000000\n");
  std::remove(path.c_str());
}

// Registers an enum type `tname` with members carrying explicit ordinal values,
// and marks each element of array `name` as that enum type, so the array is a
// genuine unpacked array of an enumerated type.
void SetupEnumMem(SimFixture& f, const char* name, const char* tname,
                  const std::vector<std::pair<const char*, uint64_t>>& members,
                  int lo, int size, uint32_t width) {
  EnumTypeInfo info;
  info.type_name = tname;
  for (auto& m : members) {
    info.members.push_back({m.first, m.second});
  }
  f.ctx.RegisterEnumType(tname, info);
  SetupMem(f, name, lo, size, width, /*four_state=*/false);
  for (int i = 0; i < size; ++i) {
    std::string nm = std::string(name) + "[" + std::to_string(lo + i) + "]";
    auto* s = f.arena.AllocString(nm.c_str(), nm.size());
    f.ctx.SetVariableEnumType(std::string_view(s, nm.size()), tname);
  }
}

// §21.5.2: for an enumerated array, the file holds each element's ordinal value
// (the member's underlying integer value, see 6.19). The members here have
// values 2, 5, and 9 -- deliberately not their 0,1,2 declaration positions --
// so the dump shows the ordinal values rather than positions or names.
TEST(IoSystemTaskTest, EnumeratedArrayWritesOrdinalValues) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_test_21_05_02_enum.txt";
  SetupEnumMem(f, "states", "state_e", {{"RED", 2}, {"GREEN", 5}, {"BLUE", 9}},
               0, 3, 8);
  // Element values are the members' ordinal (underlying) values.
  Cell(f, "states", 0)->value = MakeLogic4VecVal(f.arena, 8, 2);  // RED
  Cell(f, "states", 1)->value = MakeLogic4VecVal(f.arena, 8, 5);  // GREEN
  Cell(f, "states", 2)->value = MakeLogic4VecVal(f.arena, 8, 9);  // BLUE

  Writemem(f, "$writememh", path, "states");

  // Ordinal values 2, 5, 9 -- not positions 0, 1, 2.
  EXPECT_EQ(ReadFile(path), "02\n05\n09\n");
  std::remove(path.c_str());
}

}  // namespace
