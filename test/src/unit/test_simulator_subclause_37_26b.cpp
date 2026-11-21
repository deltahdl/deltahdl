#include <gtest/gtest.h>

#include <array>
#include <string>
#include <utility>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

struct Aggregate {
  const char* name;
  std::vector<std::string> members;
  int packed;
  int tagged;
  int soft;
  bool is_union;
};

constexpr const char* kVariables =
    "  struct { logic a; int b; } us;\n"
    "  struct packed { logic a; logic [1:0] b; } ps;\n"
    "  union { int i; logic [3:0] w; } uu;\n"
    "  union packed { logic [3:0] x; logic [3:0] y; } pu;\n"
    "  union tagged { int i; bit b; } tu;\n"
    "  union soft packed { logic [3:0] a; logic [1:0] b; } su;\n";

const std::vector<Aggregate>& Variables() {
  static const std::vector<Aggregate> kAll = {
      {"us", {"a", "b"}, 0, 0, 0, false}, {"ps", {"a", "b"}, 1, 0, 0, false},
      {"uu", {"i", "w"}, 0, 0, 0, true},  {"pu", {"x", "y"}, 1, 0, 0, true},
      {"tu", {"b", "i"}, 0, 1, 0, true},  {"su", {"a", "b"}, 1, 0, 1, true}};
  return kAll;
}

constexpr const char* kNets =
    "  wire struct { logic a; logic [1:0] b; } nus;\n"
    "  wire struct packed { logic a; logic [1:0] b; } nps;\n"
    "  wire union { logic [3:0] i; logic [1:0] w; } nuu;\n"
    "  wire union packed { logic [3:0] x; logic [3:0] y; } npu;\n"
    "  wire union tagged packed { logic [3:0] i; logic [3:0] b; } ntu;\n"
    "  wire union soft packed { logic [3:0] a; logic [1:0] b; } nsu;\n";

const std::vector<Aggregate>& Nets() {
  static const std::vector<Aggregate> kAll = {
      {"nus", {"a", "b"}, 0, 0, 0, false}, {"nps", {"a", "b"}, 1, 0, 0, false},
      {"nuu", {"i", "w"}, 0, 0, 0, true},  {"npu", {"x", "y"}, 1, 0, 0, true},
      {"ntu", {"b", "i"}, 1, 1, 0, true},  {"nsu", {"a", "b"}, 1, 0, 1, true}};
  return kAll;
}

std::string InModule(const std::string& decls) {
  return "module top;\n" + decls + "endmodule\n";
}

std::string InPackage(const std::string& decls) {
  return "package pk;\n" + decls + "endpackage\nmodule top; endmodule\n";
}

std::string InCompilationUnit(const std::string& decls) {
  return decls + "module top; endmodule\n";
}

std::string InInterface(const std::string& decls) {
  return "interface ifc;\n" + decls +
         "endinterface\nmodule top; ifc i(); endmodule\n";
}

std::string InProgram(const std::string& decls) {
  return "program prg;\n" + decls +
         "endprogram\nmodule top; prg g(); endmodule\n";
}

std::string InGenerateBlock(const std::string& decls) {
  return "module top;\n  if (1) begin : blk\n" + decls + "  end\nendmodule\n";
}

std::string InClass(const std::string& decls) {
  return "module top;\n  class C;\n" + decls +
         "  endclass\n  C c = new;\nendmodule\n";
}

std::string InTask(const std::string& decls) {
  return "module top;\n  task t;\n" + decls + "  endtask\nendmodule\n";
}

std::string InFunction(const std::string& decls) {
  return "module top;\n  function void f();\n" + decls +
         "  endfunction\nendmodule\n";
}

using Finder = vpiHandle (*)(const char*);

class AggregatesOfARun : public VpiDesignRun {
 protected:
  static vpiHandle CompilationUnit() {
    for (vpiHandle scope : ObjectsOf(vpiPackage, nullptr)) {
      if (vpi_get(vpiUnit, scope) == 1) return scope;
    }
    return nullptr;
  }

  static vpiHandle ItemOf(vpiHandle scope, const char* name) {
    if (scope == nullptr) return nullptr;
    vpiHandle variable = Named(vpiVariables, scope, name);
    return variable != nullptr ? variable : Named(vpiNet, scope, name);
  }

  static vpiHandle InTop(const char* name) {
    return By(std::string("top.") + name);
  }
  static vpiHandle InPk(const char* name) { return ItemOf(By("pk"), name); }
  static vpiHandle InUnit(const char* name) {
    return ItemOf(CompilationUnit(), name);
  }
  static vpiHandle InInterfaceInstance(const char* name) {
    return By(std::string("top.i.") + name);
  }
  static vpiHandle InProgramInstance(const char* name) {
    return By(std::string("top.g.") + name);
  }
  static vpiHandle InBlk(const char* name) {
    return By(std::string("top.blk.") + name);
  }
  static vpiHandle InObject(const char* name) {
    return ItemOf(vpi_handle(vpiClassObj, By("top.c")), name);
  }
  static vpiHandle InT(const char* name) {
    return ItemOf(Named(vpiTaskFunc, By("top"), "t"), name);
  }
  static vpiHandle InF(const char* name) {
    return ItemOf(Named(vpiTaskFunc, By("top"), "f"), name);
  }

  static bool Same(vpiHandle a, vpiHandle b) {
    return a != nullptr && b != nullptr && vpi_compare_objects(a, b) != 0;
  }

  static void ExpectMembersUnder(vpiHandle holder,
                                 const std::vector<std::string>& names) {
    ASSERT_NE(holder, nullptr);
    EXPECT_EQ(NamesOf(vpiMember, holder), names);
    for (vpiHandle member : ObjectsOf(vpiMember, holder)) {
      EXPECT_TRUE(Same(vpi_handle(vpiParent, member), holder));
    }
  }

  static void ExpectMembersOfEach(const std::vector<Aggregate>& all,
                                  Finder find) {
    for (const Aggregate& each : all) {
      SCOPED_TRACE(each.name);
      ExpectMembersUnder(find(each.name), each.members);
    }
  }

  static void ExpectPackedOfEach(const std::vector<Aggregate>& all,
                                 Finder find) {
    for (const Aggregate& each : all) {
      vpiHandle aggregate = find(each.name);
      ASSERT_NE(aggregate, nullptr) << each.name;
      EXPECT_EQ(vpi_get(vpiPacked, aggregate), each.packed) << each.name;
    }
  }

  static void ExpectTaggedAndSoftOfEachUnion(const std::vector<Aggregate>& all,
                                             Finder find) {
    for (const Aggregate& each : all) {
      if (!each.is_union) continue;
      vpiHandle aggregate = find(each.name);
      ASSERT_NE(aggregate, nullptr) << each.name;
      EXPECT_EQ(vpi_get(vpiTagged, aggregate), each.tagged) << each.name;
      EXPECT_EQ(vpi_get(vpiSoft, aggregate), each.soft) << each.name;
    }
  }

  static void ExpectNestedMembers(vpiHandle outer, int struct_kind,
                                  int union_kind) {
    ASSERT_NE(outer, nullptr);
    vpiHandle inner = Named(vpiMember, outer, "s");
    ASSERT_NE(inner, nullptr);
    EXPECT_EQ(vpi_get(vpiType, inner), struct_kind);
    ExpectMembersUnder(inner, {"a", "b"});
    vpiHandle overlay = Named(vpiMember, outer, "u");
    ASSERT_NE(overlay, nullptr);
    EXPECT_EQ(vpi_get(vpiType, overlay), union_kind);
    ExpectMembersUnder(overlay, {"x", "y"});
  }
};

TEST_F(AggregatesOfARun, AModulesStructAndUnionVarsReachTheirMembers) {
  Run(InModule(kVariables));
  ExpectMembersOfEach(Variables(), &InTop);
}

TEST_F(AggregatesOfARun, AModulesStructAndUnionVarsReportWhetherPacked) {
  Run(InModule(kVariables));
  ExpectPackedOfEach(Variables(), &InTop);
}

TEST_F(AggregatesOfARun, AModulesUnionVarsReportTaggedAndSoft) {
  Run(InModule(kVariables));
  ExpectTaggedAndSoftOfEachUnion(Variables(), &InTop);
}

TEST_F(AggregatesOfARun,
       DISABLED_APackagesStructAndUnionVarsReachTheirMembers) {
  Run(InPackage(kVariables));
  ExpectMembersOfEach(Variables(), &InPk);
}

TEST_F(AggregatesOfARun, APackagesStructAndUnionVarsReportWhetherPacked) {
  Run(InPackage(kVariables));
  ExpectPackedOfEach(Variables(), &InPk);
}

TEST_F(AggregatesOfARun, DISABLED_APackagesUnionVarsReportTaggedAndSoft) {
  Run(InPackage(kVariables));
  ExpectTaggedAndSoftOfEachUnion(Variables(), &InPk);
}

TEST_F(AggregatesOfARun, DISABLED_TheUnitsStructAndUnionVarsReachTheirMembers) {
  Run(InCompilationUnit(kVariables));
  ExpectMembersOfEach(Variables(), &InUnit);
}

TEST_F(AggregatesOfARun, TheUnitsStructAndUnionVarsReportWhetherPacked) {
  Run(InCompilationUnit(kVariables));
  ExpectPackedOfEach(Variables(), &InUnit);
}

TEST_F(AggregatesOfARun, DISABLED_TheUnitsUnionVarsReportTaggedAndSoft) {
  Run(InCompilationUnit(kVariables));
  ExpectTaggedAndSoftOfEachUnion(Variables(), &InUnit);
}

TEST_F(AggregatesOfARun, AnInterfacesStructAndUnionVarsReachTheirMembers) {
  Run(InInterface(kVariables));
  ExpectMembersOfEach(Variables(), &InInterfaceInstance);
}

TEST_F(AggregatesOfARun, AnInterfacesStructAndUnionVarsReportWhetherPacked) {
  Run(InInterface(kVariables));
  ExpectPackedOfEach(Variables(), &InInterfaceInstance);
}

TEST_F(AggregatesOfARun, AnInterfacesUnionVarsReportTaggedAndSoft) {
  Run(InInterface(kVariables));
  ExpectTaggedAndSoftOfEachUnion(Variables(), &InInterfaceInstance);
}

TEST_F(AggregatesOfARun, AProgramsStructAndUnionVarsReachTheirMembers) {
  Run(InProgram(kVariables));
  ExpectMembersOfEach(Variables(), &InProgramInstance);
}

TEST_F(AggregatesOfARun, AProgramsStructAndUnionVarsReportWhetherPacked) {
  Run(InProgram(kVariables));
  ExpectPackedOfEach(Variables(), &InProgramInstance);
}

TEST_F(AggregatesOfARun, AProgramsUnionVarsReportTaggedAndSoft) {
  Run(InProgram(kVariables));
  ExpectTaggedAndSoftOfEachUnion(Variables(), &InProgramInstance);
}

TEST_F(AggregatesOfARun, AGenerateBlocksStructAndUnionVarsReachTheirMembers) {
  Run(InGenerateBlock(kVariables));
  ExpectMembersOfEach(Variables(), &InBlk);
}

TEST_F(AggregatesOfARun, AGenerateBlocksStructAndUnionVarsReportWhetherPacked) {
  Run(InGenerateBlock(kVariables));
  ExpectPackedOfEach(Variables(), &InBlk);
}

TEST_F(AggregatesOfARun, AGenerateBlocksUnionVarsReportTaggedAndSoft) {
  Run(InGenerateBlock(kVariables));
  ExpectTaggedAndSoftOfEachUnion(Variables(), &InBlk);
}

TEST_F(AggregatesOfARun,
       DISABLED_AClassesStructAndUnionPropertiesReachTheirMembers) {
  Run(InClass(kVariables));
  ExpectMembersOfEach(Variables(), &InObject);
}

TEST_F(AggregatesOfARun,
       DISABLED_AClassesStructAndUnionPropertiesReportWhetherPacked) {
  Run(InClass(kVariables));
  ExpectPackedOfEach(Variables(), &InObject);
}

TEST_F(AggregatesOfARun, DISABLED_AClassesUnionPropertiesReportTaggedAndSoft) {
  Run(InClass(kVariables));
  ExpectTaggedAndSoftOfEachUnion(Variables(), &InObject);
}

TEST_F(AggregatesOfARun, DISABLED_ATasksStructAndUnionVarsReachTheirMembers) {
  Run(InTask(kVariables));
  ExpectMembersOfEach(Variables(), &InT);
}

TEST_F(AggregatesOfARun, DISABLED_ATasksStructAndUnionVarsReportWhetherPacked) {
  Run(InTask(kVariables));
  ExpectPackedOfEach(Variables(), &InT);
}

TEST_F(AggregatesOfARun, DISABLED_ATasksUnionVarsReportTaggedAndSoft) {
  Run(InTask(kVariables));
  ExpectTaggedAndSoftOfEachUnion(Variables(), &InT);
}

TEST_F(AggregatesOfARun,
       DISABLED_AFunctionsStructAndUnionVarsReachTheirMembers) {
  Run(InFunction(kVariables));
  ExpectMembersOfEach(Variables(), &InF);
}

TEST_F(AggregatesOfARun,
       DISABLED_AFunctionsStructAndUnionVarsReportWhetherPacked) {
  Run(InFunction(kVariables));
  ExpectPackedOfEach(Variables(), &InF);
}

TEST_F(AggregatesOfARun, DISABLED_AFunctionsUnionVarsReportTaggedAndSoft) {
  Run(InFunction(kVariables));
  ExpectTaggedAndSoftOfEachUnion(Variables(), &InF);
}

TEST_F(AggregatesOfARun, AModulesStructAndUnionNetsReachTheirMembers) {
  Run(InModule(kNets));
  ExpectMembersOfEach(Nets(), &InTop);
}

TEST_F(AggregatesOfARun, AModulesStructAndUnionNetsReportWhetherPacked) {
  Run(InModule(kNets));
  ExpectPackedOfEach(Nets(), &InTop);
}

TEST_F(AggregatesOfARun, AModulesUnionNetsReportTaggedAndSoft) {
  Run(InModule(kNets));
  ExpectTaggedAndSoftOfEachUnion(Nets(), &InTop);
}

TEST_F(AggregatesOfARun,
       DISABLED_APackagesStructAndUnionNetsReachTheirMembers) {
  Run(InPackage(kNets));
  ExpectMembersOfEach(Nets(), &InPk);
}

TEST_F(AggregatesOfARun,
       DISABLED_APackagesStructAndUnionNetsReportWhetherPacked) {
  Run(InPackage(kNets));
  ExpectPackedOfEach(Nets(), &InPk);
}

TEST_F(AggregatesOfARun, DISABLED_APackagesUnionNetsReportTaggedAndSoft) {
  Run(InPackage(kNets));
  ExpectTaggedAndSoftOfEachUnion(Nets(), &InPk);
}

TEST_F(AggregatesOfARun, DISABLED_TheUnitsStructAndUnionNetsReachTheirMembers) {
  Run(InCompilationUnit(kNets));
  ExpectMembersOfEach(Nets(), &InUnit);
}

TEST_F(AggregatesOfARun,
       DISABLED_TheUnitsStructAndUnionNetsReportWhetherPacked) {
  Run(InCompilationUnit(kNets));
  ExpectPackedOfEach(Nets(), &InUnit);
}

TEST_F(AggregatesOfARun, DISABLED_TheUnitsUnionNetsReportTaggedAndSoft) {
  Run(InCompilationUnit(kNets));
  ExpectTaggedAndSoftOfEachUnion(Nets(), &InUnit);
}

TEST_F(AggregatesOfARun, AnInterfacesStructAndUnionNetsReachTheirMembers) {
  Run(InInterface(kNets));
  ExpectMembersOfEach(Nets(), &InInterfaceInstance);
}

TEST_F(AggregatesOfARun, AnInterfacesStructAndUnionNetsReportWhetherPacked) {
  Run(InInterface(kNets));
  ExpectPackedOfEach(Nets(), &InInterfaceInstance);
}

TEST_F(AggregatesOfARun, AnInterfacesUnionNetsReportTaggedAndSoft) {
  Run(InInterface(kNets));
  ExpectTaggedAndSoftOfEachUnion(Nets(), &InInterfaceInstance);
}

TEST_F(AggregatesOfARun, AProgramsStructAndUnionNetsReachTheirMembers) {
  Run(InProgram(kNets));
  ExpectMembersOfEach(Nets(), &InProgramInstance);
}

TEST_F(AggregatesOfARun, AProgramsStructAndUnionNetsReportWhetherPacked) {
  Run(InProgram(kNets));
  ExpectPackedOfEach(Nets(), &InProgramInstance);
}

TEST_F(AggregatesOfARun, AProgramsUnionNetsReportTaggedAndSoft) {
  Run(InProgram(kNets));
  ExpectTaggedAndSoftOfEachUnion(Nets(), &InProgramInstance);
}

TEST_F(AggregatesOfARun, AGenerateBlocksStructAndUnionNetsReachTheirMembers) {
  Run(InGenerateBlock(kNets));
  ExpectMembersOfEach(Nets(), &InBlk);
}

TEST_F(AggregatesOfARun, AGenerateBlocksStructAndUnionNetsReportWhetherPacked) {
  Run(InGenerateBlock(kNets));
  ExpectPackedOfEach(Nets(), &InBlk);
}

TEST_F(AggregatesOfARun, AGenerateBlocksUnionNetsReportTaggedAndSoft) {
  Run(InGenerateBlock(kNets));
  ExpectTaggedAndSoftOfEachUnion(Nets(), &InBlk);
}

TEST_F(AggregatesOfARun, ANestedStructOrUnionVarReachesItsOwnMembers) {
  Run("module top;\n"
      "  struct { struct { logic a; int b; } s;\n"
      "    union packed { logic [1:0] x; logic [1:0] y; } u;\n"
      "    union { int i; logic [3:0] w; } v; int c; } o;\n"
      "  struct packed { struct packed { logic a; logic b; } s;\n"
      "    union packed { logic [1:0] x; logic [1:0] y; } u; } p;\n"
      "endmodule\n");
  ExpectMembersUnder(By("top.o"), {"c", "s", "u", "v"});
  ExpectNestedMembers(By("top.o"), vpiStructVar, vpiUnionVar);
  vpiHandle overlay = Named(vpiMember, By("top.o"), "v");
  EXPECT_EQ(vpi_get(vpiType, overlay), vpiUnionVar);
  ExpectMembersUnder(overlay, {"i", "w"});
  ExpectMembersUnder(By("top.p"), {"s", "u"});
  ExpectNestedMembers(By("top.p"), vpiStructVar, vpiUnionVar);
}

TEST_F(AggregatesOfARun, ANestedStructOrUnionNetReachesItsOwnMembers) {
  Run("module top;\n"
      "  wire struct { struct { logic a; logic [1:0] b; } s;\n"
      "    union { logic [1:0] x; logic y; } u; logic c; } o;\n"
      "  wire struct packed { struct packed { logic a; logic b; } s;\n"
      "    union packed { logic [1:0] x; logic [1:0] y; } u; } p;\n"
      "endmodule\n");
  ExpectMembersUnder(By("top.o"), {"c", "s", "u"});
  ExpectNestedMembers(By("top.o"), vpiStructNet, vpiUnionNet);
  ExpectMembersUnder(By("top.p"), {"s", "u"});
  ExpectNestedMembers(By("top.p"), vpiStructNet, vpiUnionNet);
}

constexpr const char* kUnpackedAggregates =
    "typedef struct { logic a; logic [1:0] b; } s_t;\n"
    "typedef union { logic [3:0] i; logic [1:0] w; } u_t;\n"
    "module top;\n"
    "  s_t sv = '{1'b1, 2'b11};\n"
    "  u_t uv;\n"
    "  wire s_t sn;\n"
    "  wire u_t un;\n"
    "  wire s_t sw;\n"
    "  wire u_t uw;\n"
    "  assign sn.a = 1'b1;\n"
    "  assign sn.b = 2'b11;\n"
    "  assign un.i = 4'b1011;\n"
    "  initial uv.i = 4'b1011;\n"
    "endmodule\n";

constexpr const char* kWholeAggregates[] = {"top.sv", "top.uv", "top.sn",
                                            "top.un"};

constexpr int kValueFormats[] = {
    vpiBinStrVal,      vpiOctStrVal,   vpiDecStrVal,    vpiHexStrVal,
    vpiScalarVal,      vpiIntVal,      vpiRealVal,      vpiStringVal,
    vpiVectorVal,      vpiStrengthVal, vpiTimeVal,      vpiObjTypeVal,
    vpiShortIntVal,    vpiLongIntVal,  vpiShortRealVal, vpiRawTwoStateVal,
    vpiRawFourStateVal};

struct ZeroBuffers {
  std::array<s_vpi_vecval, 4> vector{};
  s_vpi_time time = {vpiSimTime, 0, 0, 0.0};
  s_vpi_strengthval strength = {vpi0, vpiStrongDrive, vpiStrongDrive};
  std::array<PLI_BYTE8, 32> raw{};
  std::array<PLI_BYTE8, 2> text = {'0', '\0'};
};

s_vpi_value ZeroValueOf(int format, ZeroBuffers& buffers) {
  s_vpi_value value = {};
  value.format = format;
  if (format == vpiVectorVal) {
    value.value.vector = buffers.vector.data();
  } else if (format == vpiTimeVal) {
    value.value.time = &buffers.time;
  } else if (format == vpiStrengthVal) {
    value.value.strength = &buffers.strength;
  } else if (format == vpiRawTwoStateVal || format == vpiRawFourStateVal) {
    value.value.misc = buffers.raw.data();
  } else if (format == vpiScalarVal) {
    value.value.scalar = vpi0;
  } else if (format != vpiIntVal && format != vpiRealVal &&
             format != vpiShortIntVal && format != vpiLongIntVal &&
             format != vpiShortRealVal && format != vpiObjTypeVal) {
    value.value.str = buffers.text.data();
  }
  return value;
}

TEST_F(AggregatesOfARun, AWholeUnpackedStructOrUnionIsReadInNoFormat) {
  Run(kUnpackedAggregates);
  ZeroBuffers buffers;
  for (const char* name : kWholeAggregates) {
    vpiHandle aggregate = By(name);
    ASSERT_NE(aggregate, nullptr) << name;
    for (int format : kValueFormats) {
      s_vpi_value value = ZeroValueOf(format, buffers);
      vpi_get_value(aggregate, &value);
      s_vpi_error_info info = {};
      const PLI_INT32 kLevel = vpi_chk_error(&info);
      EXPECT_NE(kLevel, 0) << name << " format " << format;
    }
  }
}

TEST_F(AggregatesOfARun, AWholeUnpackedStructOrUnionIsWrittenInNoFormat) {
  Run(kUnpackedAggregates);
  ZeroBuffers buffers;
  for (const char* name : kWholeAggregates) {
    vpiHandle aggregate = By(name);
    ASSERT_NE(aggregate, nullptr) << name;
    for (int format : kValueFormats) {
      s_vpi_value value = ZeroValueOf(format, buffers);
      vpi_put_value(aggregate, &value, nullptr, vpiNoDelay);
      s_vpi_error_info info = {};
      const PLI_INT32 kLevel = vpi_chk_error(&info);
      EXPECT_NE(kLevel, 0) << name << " format " << format;
    }
  }
  EXPECT_EQ(IntegerOf(By("top.sv.a")), 1);
  EXPECT_EQ(IntegerOf(By("top.sv.b")), 3);
  EXPECT_EQ(IntegerOf(By("top.uv.i")), 11);
  EXPECT_EQ(IntegerOf(By("top.sn.a")), 1);
  EXPECT_EQ(IntegerOf(By("top.sn.b")), 3);
  EXPECT_EQ(IntegerOf(By("top.un.i")), 11);
}

TEST_F(AggregatesOfARun, AMemberOfAnUnpackedStructOrUnionIsRead) {
  Run(kUnpackedAggregates);
  const std::pair<const char*, int> kMembers[] = {
      {"top.sv.b", 3}, {"top.uv.i", 11}, {"top.sn.b", 3}, {"top.un.i", 11}};
  for (const auto& [name, expected] : kMembers) {
    vpiHandle member = By(name);
    ASSERT_NE(member, nullptr) << name;
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(member, &value);
    s_vpi_error_info info = {};
    const PLI_INT32 kLevel = vpi_chk_error(&info);
    EXPECT_EQ(kLevel, 0) << name;
    EXPECT_EQ(value.value.integer, expected) << name;
  }
}

TEST_F(AggregatesOfARun, AMemberOfAnUnpackedStructOrUnionIsWritten) {
  Run(kUnpackedAggregates);
  const std::pair<const char*, int> kMembers[] = {
      {"top.sv.b", 2}, {"top.uv.i", 6}, {"top.sw.b", 2}, {"top.uw.i", 6}};
  for (const auto& [name, written] : kMembers) {
    vpiHandle member = By(name);
    ASSERT_NE(member, nullptr) << name;
    s_vpi_value value = {};
    value.format = vpiIntVal;
    value.value.integer = written;
    vpi_put_value(member, &value, nullptr, vpiNoDelay);
    s_vpi_error_info info = {};
    const PLI_INT32 kLevel = vpi_chk_error(&info);
    EXPECT_EQ(kLevel, 0) << name;
    EXPECT_EQ(IntegerOf(member), written) << name;
  }
}

}  // namespace
}  // namespace delta
