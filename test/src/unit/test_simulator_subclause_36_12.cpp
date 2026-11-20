#include <gtest/gtest.h>

#include <array>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

extern "C" {
vpiHandle vpi_iterate_1364v1995(PLI_INT32 type, vpiHandle ref);
vpiHandle vpi_iterate_1364v2001(PLI_INT32 type, vpiHandle ref);
vpiHandle vpi_iterate_1364v2005(PLI_INT32 type, vpiHandle ref);
vpiHandle vpi_iterate_1800v2005(PLI_INT32 type, vpiHandle ref);
vpiHandle vpi_iterate_1800v2009(PLI_INT32 type, vpiHandle ref);
vpiHandle vpi_iterate_1800v2012(PLI_INT32 type, vpiHandle ref);
}

namespace delta {
namespace {

class VpiCompatibility : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  std::vector<vpiHandle> ScanAll(vpiHandle it) {
    std::vector<vpiHandle> seen;
    if (it == nullptr) return seen;
    while (vpiHandle h = vpi_scan(it)) seen.push_back(h);
    return seen;
  }

  VpiContext ctx_;
};

TEST_F(VpiCompatibility, ARegIterationOnAnArrayRetrievesElementsOfEveryKind) {
  VpiObject reg_word;
  reg_word.type = vpiReg;
  VpiObject integer_word;
  integer_word.type = vpiIntegerVar;
  VpiObject time_word;
  time_word.type = vpiTimeVar;

  VpiObject array;
  array.type = vpiRegArray;
  array.children = {&reg_word, &integer_word, &time_word};

  std::vector<vpiHandle> seen =
      ScanAll(vpi_iterate(vpiReg, VpiHandleOf(&array)));
  ASSERT_EQ(seen.size(), 3u);
  EXPECT_EQ(VpiObjectOf(seen[0]), &reg_word);
  EXPECT_EQ(VpiObjectOf(seen[1]), &integer_word);
  EXPECT_EQ(VpiObjectOf(seen[2]), &time_word);
}

TEST_F(VpiCompatibility, ARegIterationOnAScopeIsUnaffected) {
  VpiObject reg;
  reg.type = vpiReg;
  VpiObject int_var;
  int_var.type = vpiIntegerVar;

  VpiObject scope;
  scope.type = vpiModule;
  scope.children = {&reg, &int_var};

  std::vector<vpiHandle> seen =
      ScanAll(vpi_iterate(vpiReg, VpiHandleOf(&scope)));
  ASSERT_EQ(seen.size(), 1u);
  EXPECT_EQ(VpiObjectOf(seen[0]), &reg);
}

TEST_F(VpiCompatibility, AVariablesIterationIncludesRegsAndRegArrays) {
  VpiObject reg;
  reg.type = vpiReg;
  VpiObject array;
  array.type = vpiRegArray;

  VpiObject scope;
  scope.type = vpiModule;
  scope.children = {&reg, &array};

  std::vector<vpiHandle> seen =
      ScanAll(vpi_iterate(vpiVariables, VpiHandleOf(&scope)));
  ASSERT_EQ(seen.size(), 2u);
  EXPECT_EQ(VpiObjectOf(seen[0]), &reg);
  EXPECT_EQ(VpiObjectOf(seen[1]), &array);
}

TEST_F(VpiCompatibility, ARegArrayIterationIncludesArraysOfEveryVariable) {
  VpiObject int_word;
  int_word.type = vpiIntegerVar;
  VpiObject int_array;
  int_array.type = vpiRegArray;
  int_array.children = {&int_word};

  VpiObject real_word;
  real_word.type = vpiRealVar;
  VpiObject real_array;
  real_array.type = vpiRegArray;
  real_array.children = {&real_word};

  VpiObject scope;
  scope.type = vpiModule;
  scope.children = {&int_array, &real_array};

  std::vector<vpiHandle> seen =
      ScanAll(vpi_iterate(vpiRegArray, VpiHandleOf(&scope)));
  ASSERT_EQ(seen.size(), 2u);
  EXPECT_EQ(VpiObjectOf(seen[0]), &int_array);
  EXPECT_EQ(VpiObjectOf(seen[1]), &real_array);
}

TEST_F(VpiCompatibility, MemoryAndMemoryWordAreRelationsRatherThanObjects) {
  VpiObject word;
  word.type = vpiReg;
  VpiObject memory;
  memory.type = vpiRegArray;
  memory.children = {&word};

  VpiObject scope;
  scope.type = vpiModule;
  scope.children = {&memory};

  std::vector<vpiHandle> memories =
      ScanAll(vpi_iterate(vpiMemory, VpiHandleOf(&scope)));
  ASSERT_EQ(memories.size(), 1u);
  EXPECT_EQ(VpiObjectOf(memories[0]), &memory);
  EXPECT_EQ(vpi_get(vpiType, memories[0]), vpiRegArray);

  std::vector<vpiHandle> words =
      ScanAll(vpi_iterate(vpiMemoryWord, VpiHandleOf(&memory)));
  ASSERT_EQ(words.size(), 1u);
  EXPECT_EQ(VpiObjectOf(words[0]), &word);
  EXPECT_EQ(vpi_get(vpiType, words[0]), vpiReg);
}

int g_array_kind = 0;
int g_integer_kind = 0;
int g_real_kind = 0;
int g_reg_kind = 0;
int g_arrays_seen = 0;

PLI_INT32 InspectKindsCalltf(PLI_BYTE8*) {
  vpiHandle mod = vpi_handle_by_name(VpiText("m1"), nullptr);
  if (mod == nullptr) return 0;

  vpiHandle mem = vpi_handle_by_name(VpiText("m1.mem"), nullptr);
  if (mem != nullptr) g_array_kind = vpi_get(vpiType, mem);
  vpiHandle i = vpi_handle_by_name(VpiText("m1.i"), nullptr);
  if (i != nullptr) g_integer_kind = vpi_get(vpiType, i);
  vpiHandle r = vpi_handle_by_name(VpiText("m1.r"), nullptr);
  if (r != nullptr) g_real_kind = vpi_get(vpiType, r);
  vpiHandle b = vpi_handle_by_name(VpiText("m1.b"), nullptr);
  if (b != nullptr) g_reg_kind = vpi_get(vpiType, b);

  vpiHandle it = vpi_iterate(vpiRegArray, mod);
  if (it == nullptr) return 0;
  while (vpi_scan(it) != nullptr) ++g_arrays_seen;
  return 0;
}

void RegisterKindProbe() {
  g_array_kind = 0;
  g_integer_kind = 0;
  g_real_kind = 0;
  g_reg_kind = 0;
  g_arrays_seen = 0;

  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$probe");
  data.calltf = &InspectKindsCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
}

TEST_F(VpiCompatibility, ADesignsVariablesCarryTheKindsTheTableRequires) {
  RegisterKindProbe();

  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg [7:0] mem [0:3];\n"
      "  integer i;\n"
      "  real r;\n"
      "  reg b;\n"
      "endmodule\n"
      "module t;\n"
      "  m m1();\n"
      "  initial $probe;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  EXPECT_EQ(g_array_kind, vpiRegArray);
  EXPECT_EQ(g_integer_kind, vpiIntegerVar);
  EXPECT_EQ(g_real_kind, vpiRealVar);
  EXPECT_EQ(g_reg_kind, vpiReg);
  EXPECT_EQ(g_arrays_seen, 1);
}

using VpiIterateRoutine = vpiHandle (*)(PLI_INT32, vpiHandle);

constexpr std::array<VpiIterateRoutine, 2> kThe1364WithoutRegsIterates = {
    vpi_iterate_1364v1995, vpi_iterate_1364v2005};
constexpr std::array<VpiIterateRoutine, 3> kThe1800Iterates = {
    vpi_iterate_1800v2005, vpi_iterate_1800v2009, vpi_iterate_1800v2012};
constexpr std::array<int, 2> kThe1364WithoutRegsModes = {vpiMode1364v1995,
                                                         vpiMode1364v2005};

class VpiTableRowsPerMode : public ::testing::Test {
 protected:
  void SetUp() override {
    SetGlobalVpiContext(&ctx_);
    Fill(memory_, vpiRegArray, word_, vpiReg);
    Fill(integer_array_, vpiRegArray, integer_word_, vpiIntegerVar);
    Fill(time_array_, vpiRegArray, time_word_, vpiTimeVar);
    Fill(real_array_, vpiRegArray, real_word_, vpiRealVar);
    mixed_.type = vpiRegArray;
    mixed_reg_.type = vpiReg;
    mixed_integer_.type = vpiIntegerVar;
    mixed_reg_.parent = &mixed_;
    mixed_integer_.parent = &mixed_;
    mixed_.children = {&mixed_reg_, &mixed_integer_};
    reg_.type = vpiReg;
    int_var_.type = vpiIntVar;
    scope_.type = vpiModule;
    scope_.children = {&reg_,        &memory_,     &integer_array_,
                       &time_array_, &real_array_, &int_var_};
    for (VpiObject* child : scope_.children) child->parent = &scope_;
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  static void Fill(VpiObject& array, int array_type, VpiObject& word,
                   int word_type) {
    array.type = array_type;
    word.type = word_type;
    word.parent = &array;
    array.children = {&word};
  }

  static std::vector<VpiObject*> Reached(vpiHandle it) {
    std::vector<VpiObject*> seen;
    if (it == nullptr) return seen;
    while (vpiHandle h = vpi_scan(it)) seen.push_back(VpiObjectOf(h));
    return seen;
  }

  std::vector<VpiObject*> AllVariables() {
    return {&reg_,        &memory_,     &integer_array_,
            &time_array_, &real_array_, &int_var_};
  }
  std::vector<VpiObject*> AllArrays() {
    return {&memory_, &integer_array_, &time_array_, &real_array_};
  }

  VpiContext ctx_;
  VpiObject scope_;
  VpiObject reg_;
  VpiObject memory_;
  VpiObject word_;
  VpiObject integer_array_;
  VpiObject integer_word_;
  VpiObject time_array_;
  VpiObject time_word_;
  VpiObject real_array_;
  VpiObject real_word_;
  VpiObject int_var_;
  VpiObject mixed_;
  VpiObject mixed_reg_;
  VpiObject mixed_integer_;
};

TEST_F(VpiTableRowsPerMode, AVariablesIterationExcludesRegsUnder1995And2005) {
  const std::vector<VpiObject*> kNoRegs = {&int_var_};
  for (VpiIterateRoutine iterate : kThe1364WithoutRegsIterates) {
    EXPECT_EQ(Reached(iterate(vpiVariables, VpiHandleOf(&scope_))), kNoRegs);
  }
  for (int mode : kThe1364WithoutRegsModes) {
    VpiContext ctx;
    SetGlobalVpiContext(&ctx);
    ASSERT_TRUE(ctx.SetDefaultCompatibilityMode(mode));
    EXPECT_EQ(Reached(vpi_iterate(vpiVariables, VpiHandleOf(&scope_))),
              kNoRegs);
  }
}

TEST_F(VpiTableRowsPerMode, AVariablesIterationIncludesRegsUnderThe1800Modes) {
  for (VpiIterateRoutine iterate : kThe1800Iterates) {
    EXPECT_EQ(Reached(iterate(vpiVariables, VpiHandleOf(&scope_))),
              AllVariables());
  }
  ASSERT_TRUE(ctx_.SetDefaultCompatibilityMode(vpiMode1800v2005));
  EXPECT_EQ(Reached(vpi_iterate(vpiVariables, VpiHandleOf(&scope_))),
            AllVariables());
}

TEST_F(VpiTableRowsPerMode, ARegIterationOnAnArrayKeepsOnlyRegsUnder1364) {
  const std::vector<VpiObject*> kOnlyRegs = {&mixed_reg_};
  for (VpiIterateRoutine iterate : kThe1364WithoutRegsIterates) {
    EXPECT_EQ(Reached(iterate(vpiReg, VpiHandleOf(&mixed_))), kOnlyRegs);
  }
  for (int mode : kThe1364WithoutRegsModes) {
    VpiContext ctx;
    SetGlobalVpiContext(&ctx);
    ASSERT_TRUE(ctx.SetDefaultCompatibilityMode(mode));
    EXPECT_EQ(Reached(vpi_iterate(vpiReg, VpiHandleOf(&mixed_))), kOnlyRegs);
  }
}

TEST_F(VpiTableRowsPerMode, ARegIterationOnAnArrayKeepsEveryKindUnder1800) {
  const std::vector<VpiObject*> kEveryKind = {&mixed_reg_, &mixed_integer_};
  for (VpiIterateRoutine iterate : kThe1800Iterates) {
    EXPECT_EQ(Reached(iterate(vpiReg, VpiHandleOf(&mixed_))), kEveryKind);
  }
  ASSERT_TRUE(ctx_.SetDefaultCompatibilityMode(vpiMode1800v2005));
  EXPECT_EQ(Reached(vpi_iterate(vpiReg, VpiHandleOf(&mixed_))), kEveryKind);
}

TEST_F(VpiTableRowsPerMode, ARegArrayIterationReachesATimeArrayNatively) {
  EXPECT_EQ(Reached(vpi_iterate(vpiRegArray, VpiHandleOf(&scope_))),
            AllArrays());
}

TEST_F(VpiTableRowsPerMode, ARegArrayIterationKeepsOnlyMemoriesUnder1364) {
  const std::vector<VpiObject*> kOnlyMemories = {&memory_};
  for (VpiIterateRoutine iterate : kThe1364WithoutRegsIterates) {
    EXPECT_EQ(Reached(iterate(vpiRegArray, VpiHandleOf(&scope_))),
              kOnlyMemories);
  }
  for (int mode : kThe1364WithoutRegsModes) {
    VpiContext ctx;
    SetGlobalVpiContext(&ctx);
    ASSERT_TRUE(ctx.SetDefaultCompatibilityMode(mode));
    EXPECT_EQ(Reached(vpi_iterate(vpiRegArray, VpiHandleOf(&scope_))),
              kOnlyMemories);
  }
}

TEST_F(VpiTableRowsPerMode, ARegArrayIterationKeepsEveryArrayUnder1800) {
  for (VpiIterateRoutine iterate : kThe1800Iterates) {
    EXPECT_EQ(Reached(iterate(vpiRegArray, VpiHandleOf(&scope_))), AllArrays());
  }
  ASSERT_TRUE(ctx_.SetDefaultCompatibilityMode(vpiMode1800v2005));
  EXPECT_EQ(Reached(vpi_iterate(vpiRegArray, VpiHandleOf(&scope_))),
            AllArrays());
}

TEST_F(VpiTableRowsPerMode, EachApplicationKeepsItsOwnModeBesideTheDefault) {
  const std::vector<VpiObject*> kNoRegs = {&int_var_};
  ASSERT_TRUE(ctx_.SetDefaultCompatibilityMode(vpiMode1800v2009));
  EXPECT_EQ(Reached(vpi_iterate_1364v2001(vpiVariables, VpiHandleOf(&scope_))),
            kNoRegs);
  EXPECT_EQ(Reached(vpi_iterate(vpiVariables, VpiHandleOf(&scope_))),
            AllVariables());
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);
  ASSERT_TRUE(ctx.SetDefaultCompatibilityMode(vpiMode1364v2001));
  EXPECT_EQ(Reached(vpi_iterate_1800v2009(vpiVariables, VpiHandleOf(&scope_))),
            AllVariables());
  EXPECT_EQ(Reached(vpi_iterate(vpiVariables, VpiHandleOf(&scope_))), kNoRegs);
}

class VpiInterfaceDeclPerMode : public ::testing::Test {
 protected:
  void SetUp() override {
    SetGlobalVpiContext(&ctx_);
    class_vif_.type = vpiVirtualInterfaceVar;
    class_defn_.type = vpiClassDefn;
    class_defn_.children = {&class_vif_};
    class_vif_.parent = &class_defn_;
    typespec_vif_.type = vpiVirtualInterfaceVar;
    typespec_.type = vpiClassTypespec;
    typespec_.children = {&typespec_vif_};
    typespec_vif_.parent = &typespec_;
    module_vif_.type = vpiVirtualInterfaceVar;
    module_.type = vpiModule;
    module_.children = {&module_vif_};
    module_vif_.parent = &module_;
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  static std::vector<int> TypesReached(vpiHandle it) {
    std::vector<int> types;
    if (it == nullptr) return types;
    while (vpiHandle h = vpi_scan(it)) types.push_back(vpi_get(vpiType, h));
    return types;
  }

  VpiContext ctx_;
  VpiObject class_defn_;
  VpiObject class_vif_;
  VpiObject typespec_;
  VpiObject typespec_vif_;
  VpiObject module_;
  VpiObject module_vif_;
};

constexpr std::array<VpiIterateRoutine, 2> kThe2005And2009Iterates = {
    vpi_iterate_1800v2005, vpi_iterate_1800v2009};
constexpr std::array<int, 2> kThe2005And2009Modes = {vpiMode1800v2005,
                                                     vpiMode1800v2009};

TEST_F(VpiInterfaceDeclPerMode, AClassTypespecReachesItsVirtualInterfaces) {
  vpiHandle it = vpi_iterate(vpiInterfaceDecl, VpiHandleOf(&typespec_));
  ASSERT_NE(it, nullptr);
  vpiHandle first = vpi_scan(it);
  EXPECT_EQ(VpiObjectOf(first), &typespec_vif_);
  EXPECT_EQ(vpi_scan(it), nullptr);
}

TEST_F(VpiInterfaceDeclPerMode,
       DISABLED_AClassDefnIterationIsAllowedUnder2005And2009) {
  for (VpiIterateRoutine iterate : kThe2005And2009Iterates) {
    EXPECT_NE(iterate(vpiInterfaceDecl, VpiHandleOf(&class_defn_)), nullptr);
  }
  for (int mode : kThe2005And2009Modes) {
    VpiContext ctx;
    SetGlobalVpiContext(&ctx);
    ASSERT_TRUE(ctx.SetDefaultCompatibilityMode(mode));
    EXPECT_NE(vpi_iterate(vpiInterfaceDecl, VpiHandleOf(&class_defn_)),
              nullptr);
  }
}

TEST_F(VpiInterfaceDeclPerMode, AClassDefnIterationIsRefusedFrom2012On) {
  EXPECT_EQ(vpi_iterate_1800v2012(vpiInterfaceDecl, VpiHandleOf(&class_defn_)),
            nullptr);
}

TEST_F(VpiInterfaceDeclPerMode,
       DISABLED_TheIterationGivesRefObjsUnder2005And2009) {
  const std::vector<int> kRefObj = {vpiRefObj};
  for (VpiIterateRoutine iterate : kThe2005And2009Iterates) {
    EXPECT_EQ(TypesReached(iterate(vpiInterfaceDecl, VpiHandleOf(&module_))),
              kRefObj);
  }
  for (int mode : kThe2005And2009Modes) {
    VpiContext ctx;
    SetGlobalVpiContext(&ctx);
    ASSERT_TRUE(ctx.SetDefaultCompatibilityMode(mode));
    EXPECT_EQ(
        TypesReached(vpi_iterate(vpiInterfaceDecl, VpiHandleOf(&module_))),
        kRefObj);
  }
}

TEST_F(VpiInterfaceDeclPerMode, TheIterationGivesVirtualInterfacesFrom2012On) {
  const std::vector<int> kVirtualInterface = {vpiVirtualInterfaceVar};
  EXPECT_EQ(TypesReached(
                vpi_iterate_1800v2012(vpiInterfaceDecl, VpiHandleOf(&module_))),
            kVirtualInterface);
}

}  // namespace
}  // namespace delta
