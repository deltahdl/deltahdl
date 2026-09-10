#include <gtest/gtest.h>

#include <vector>

#include "fixture_simulator.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.4.1 (Diagram key for objects and classes) is the key the data model
// diagrams of §37.5 onward are read with. It names five notations, and the two
// that decide what an implementation answers are the enclosures: a solid one
// holds an object, bold where the object is defined and normal where it is
// referenced, and a dotted one holds a class -- "bold italic letters in a
// dotted enclosure indicate a class definition, where the class groups other
// objects and classes". A class is that grouping and nothing else. It has no
// object of its own, so no object's vpiType is a class constant, and a relation
// drawn to a class reaches the objects the class groups.
//
// §37.17 draws `variables` as such a class, and the object definitions inside
// its enclosure are what vpiVariables names: a logic var, an int var, a string
// var, an array var and the rest. §37.12 draws the scope's vpiVariables
// relation to that class.
class VpiVariablesClass : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  std::vector<vpiHandle> ScanAll(vpiHandle it) {
    std::vector<vpiHandle> seen;
    if (it == nullptr) return seen;
    while (vpiHandle h = vpi_scan(it)) seen.push_back(h);
    return seen;
  }

  VpiContext vpi_ctx_;
};

// Claim: a relation drawn to a class reaches the objects that class groups. The
// scope holds one variable of each of three kinds §37.17 draws inside the
// `variables` enclosure, and all three come back.
TEST_F(VpiVariablesClass, TheRelationReachesEveryKindTheClassGroups) {
  VpiObject logic_var;
  logic_var.type = vpiLogicVar;
  VpiObject int_var;
  int_var.type = vpiIntVar;
  VpiObject string_var;
  string_var.type = vpiStringVar;

  VpiObject scope;
  scope.type = vpiModule;
  scope.children = {&logic_var, &int_var, &string_var};

  std::vector<vpiHandle> seen = ScanAll(vpi_iterate(vpiVariables, &scope));
  ASSERT_EQ(seen.size(), 3u);
  EXPECT_EQ(seen[0], &logic_var);
  EXPECT_EQ(seen[1], &int_var);
  EXPECT_EQ(seen[2], &string_var);
}

// Claim: the grouping is what a class is, so a class constant is not a kind an
// object has. A child stamped with the class constant itself is an object of no
// definition the standard draws, and the relation does not report it.
TEST_F(VpiVariablesClass, TheClassConstantIsNotAKindTheRelationReports) {
  VpiObject tagged_with_the_class;
  tagged_with_the_class.type = vpiVariables;

  VpiObject scope;
  scope.type = vpiModule;
  scope.children = {&tagged_with_the_class};

  EXPECT_TRUE(ScanAll(vpi_iterate(vpiVariables, &scope)).empty());
}

// Claim: an object grouped by a class reports its own definition as its type,
// never the class it is grouped by. §37.3.2 makes vpiType the object's type
// constant, and a class has no object for one to name.
TEST_F(VpiVariablesClass, AGroupedObjectReportsItsOwnDefinitionAsItsType) {
  VpiObject int_var;
  int_var.type = vpiIntVar;

  EXPECT_EQ(vpi_get(vpiType, &int_var), vpiIntVar);
  EXPECT_NE(vpi_get(vpiType, &int_var), vpiVariables);
}

// Claim: an object kind outside the enclosure is not grouped by the class, so
// the relation passes it over. A net is drawn in a class of its own (§37.16).
TEST_F(VpiVariablesClass, AnObjectOutsideTheEnclosureIsNotReached) {
  VpiObject net;
  net.type = kVpiNet;
  VpiObject logic_var;
  logic_var.type = vpiLogicVar;

  VpiObject scope;
  scope.type = vpiModule;
  scope.children = {&net, &logic_var};

  std::vector<vpiHandle> seen = ScanAll(vpi_iterate(vpiVariables, &scope));
  ASSERT_EQ(seen.size(), 1u);
  EXPECT_EQ(seen[0], &logic_var);
}

// What the application found. A calltf is a plain C function with no return
// path to the case that provoked it.
int g_vars_seen = 0;

int CountVariablesCalltf(const char*) {
  vpiHandle mod = vpi_handle_by_name("m1", nullptr);
  if (mod == nullptr) return 0;
  vpiHandle itr = vpi_iterate(vpiVariables, mod);
  if (itr == nullptr) return 0;
  while (vpi_scan(itr) != nullptr) ++g_vars_seen;
  return 0;
}

void RegisterVariableCountProbe() {
  g_vars_seen = 0;

  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = "$probe";
  data.calltf = &CountVariablesCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
}

// Claim, against a design: the objects an elaborated design puts in a scope are
// of the kinds the class groups, so the scope's vpiVariables relation reaches
// them. Matching the class constant against an object's own type reached none
// of them, VpiContext::Attach stamping a variable vpiReg.
TEST_F(VpiVariablesClass, AScopeOfADesignReachesTheVariablesItDeclares) {
  RegisterVariableCountProbe();

  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a;\n"
      "  reg b;\n"
      "endmodule\n"
      "module t;\n"
      "  m m1();\n"
      "  initial $probe;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  EXPECT_EQ(g_vars_seen, 2);
}

}  // namespace
}  // namespace delta
