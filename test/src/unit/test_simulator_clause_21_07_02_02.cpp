// §21.7.2.2: Formats of variable values

#include "fixture_vcd.h"
#include "simulator/variable.h"
#include "simulator/vcd_writer.h"

namespace delta {
namespace {

class VcdClause21070202Test : public VcdTestBase {};

TEST_F(VcdClause21070202Test, FourValueScalar) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    auto* var = arena_.Create<Variable>();
    var->value = MakeLogic4Vec(arena_, 1);
    var->value.words[0].aval = 0;
    var->value.words[0].bval = 1;
    vcd.RegisterSignal("sig", 1, var);
    vcd.EndDefinitions();
    vcd.WriteTimestamp(0);
    vcd.DumpAllValues();
  }
  auto content = ReadVcd();
  EXPECT_NE(content.find("x!"), std::string::npos);
}

TEST_F(VcdClause21070202Test, DumpChangedValuesOnlyEmitsChanged) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    auto* var_a = arena_.Create<Variable>();
    var_a->value = MakeLogic4VecVal(arena_, 1, 0);
    var_a->prev_value = MakeLogic4VecVal(arena_, 1, 0);
    auto* var_b = arena_.Create<Variable>();
    var_b->value = MakeLogic4VecVal(arena_, 1, 1);
    var_b->prev_value = MakeLogic4VecVal(arena_, 1, 0);
    vcd.RegisterSignal("a", 1, var_a);
    vcd.RegisterSignal("b", 1, var_b);
    vcd.EndDefinitions();
    vcd.WriteTimestamp(10);
    vcd.DumpChangedValues(0);
  }
  auto content = ReadVcd();
  EXPECT_NE(content.find("1\""), std::string::npos);
}

}  // namespace
}  // namespace delta
