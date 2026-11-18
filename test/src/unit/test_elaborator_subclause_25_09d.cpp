#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr const char* kDefparamMsg =
    "interface instance targeted by a defparam declared outside the interface "
    "cannot be assigned to a virtual interface";

const std::vector<Diagnostic>& Elab(ElabFixture& f, const std::string& src) {
  ElaborateSrc(src, f);
  return f.diag.Diagnostics();
}

TEST(VirtualInterfaceDefparam, ADefparamOnANestedInstanceRefusesTheOuter) {
  ElabFixture f;
  const auto& d = Elab(f,
                       "interface ibus #(parameter W = 8); endinterface\n"
                       "interface obus; ibus i(); endinterface\n"
                       "module top;\n"
                       "  obus o();\n"
                       "  obus p();\n"
                       "  defparam o.i.W = 16;\n"
                       "  virtual obus v;\n"
                       "  initial v = o;\n"
                       "  initial v = p;\n"
                       "endmodule\n");
  EXPECT_TRUE(ReportedError(d, kDefparamMsg, 8, "25.9"));
  EXPECT_FALSE(ReportedError(d, kDefparamMsg, 9, "25.9"));
}

TEST(VirtualInterfaceDefparam,
     DISABLED_ADefparamInAnotherModuleRefusesTheInstance) {
  ElabFixture f;
  const auto& d = Elab(f,
                       "interface pbus #(parameter W = 8); endinterface\n"
                       "module other; defparam top.u.W = 16; endmodule\n"
                       "module top;\n"
                       "  pbus u();\n"
                       "  pbus w();\n"
                       "  other o();\n"
                       "  virtual pbus vif;\n"
                       "  initial vif = u;\n"
                       "  initial vif = w;\n"
                       "endmodule\n");
  EXPECT_TRUE(ReportedError(d, kDefparamMsg, 8, "25.9"));
  EXPECT_FALSE(ReportedError(d, kDefparamMsg, 9, "25.9"));
}

TEST(VirtualInterfaceDefparam,
     DISABLED_ATargetedInstancePassedToAVirtualInterfaceFormalIsRefused) {
  ElabFixture f;
  const auto& d = Elab(f,
                       "interface pbus #(parameter W = 8); endinterface\n"
                       "class C;\n"
                       "  function new(virtual pbus v); endfunction\n"
                       "  task m(virtual pbus v); endtask\n"
                       "endclass\n"
                       "module top;\n"
                       "  pbus u();\n"
                       "  pbus w();\n"
                       "  defparam u.W = 16;\n"
                       "  task t(virtual pbus v); endtask\n"
                       "  function void g(virtual pbus v); endfunction\n"
                       "  C c;\n"
                       "  initial begin\n"
                       "    t(u);\n"
                       "    g(u);\n"
                       "    c = new(u);\n"
                       "    c.m(u);\n"
                       "    t(w);\n"
                       "  end\n"
                       "endmodule\n");
  for (uint32_t line : {14U, 15U, 16U, 17U}) {
    EXPECT_TRUE(ReportedError(d, kDefparamMsg, line, "25.9")) << line;
  }
  EXPECT_FALSE(ReportedError(d, kDefparamMsg, 18, "25.9"));
}

TEST(VirtualInterfaceDefparam,
     DISABLED_ATargetedInstanceAsADeclarationsInitializerIsRefused) {
  ElabFixture f;
  const auto& d = Elab(f,
                       "interface pbus #(parameter W = 8); endinterface\n"
                       "module top;\n"
                       "  pbus u();\n"
                       "  pbus w();\n"
                       "  defparam u.W = 16;\n"
                       "  virtual pbus vif = u;\n"
                       "  virtual pbus vok = w;\n"
                       "endmodule\n");
  EXPECT_TRUE(ReportedError(d, kDefparamMsg, 6, "25.9"));
  EXPECT_FALSE(ReportedError(d, kDefparamMsg, 7, "25.9"));
}

constexpr const char* kPortMsg =
    "virtual interface cannot be used as a port type";

void ExpectPortRefused(const std::string& src, const char* refused,
                       const char* accepted) {
  ElabFixture f;
  ElaborateSrc(src, f, refused);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kPortMsg, 2, "25.9"));
  ElabFixture g;
  ElaborateSrc(src, g, accepted);
  EXPECT_FALSE(ReportedError(g.diag.Diagnostics(), kPortMsg, 4, "25.9"));
}

TEST(VirtualInterfacePort, AnInterfacesPortIsRefused) {
  ExpectPortRefused(
      "interface sb; endinterface\n"
      "interface I2(input virtual sb v);\n"
      "endinterface\n"
      "interface I3(input logic a);\n"
      "endinterface\n",
      "I2", "I3");
}

TEST(VirtualInterfacePort, AProgramsPortIsRefused) {
  ExpectPortRefused(
      "interface sb; endinterface\n"
      "program p(input virtual sb v);\n"
      "endprogram\n"
      "program q(input logic a);\n"
      "endprogram\n",
      "p", "q");
}

TEST(VirtualInterfacePort, AModulesRefPortIsRefused) {
  ExpectPortRefused(
      "interface sb; endinterface\n"
      "module m(ref virtual sb v);\n"
      "endmodule\n"
      "module n(ref logic a);\n"
      "endmodule\n",
      "m", "n");
}

constexpr const char* kUnionMsg =
    "virtual interface cannot be used as a member of a union";

TEST(VirtualInterfaceUnionMember, AUnionTypedefInAPackageIsRefused) {
  ElabFixture f;
  const auto& d = Elab(f,
                       "interface sb; endinterface\n"
                       "package pk;\n"
                       "  typedef union { virtual sb v; int i; } u_t;\n"
                       "  typedef struct { virtual sb v; int i; } s_t;\n"
                       "endpackage\n");
  EXPECT_TRUE(ReportedError(d, kUnionMsg, 3, "25.9"));
  EXPECT_FALSE(ReportedError(d, kUnionMsg, 4, "25.9"));
}

TEST(VirtualInterfaceUnionMember, AUnionTypedefInAClassIsRefused) {
  ElabFixture f;
  const auto& d = Elab(f,
                       "interface sb; endinterface\n"
                       "class C;\n"
                       "  typedef union { virtual sb v; int i; } u_t;\n"
                       "  typedef struct { virtual sb v; int i; } s_t;\n"
                       "endclass\n");
  EXPECT_TRUE(ReportedError(d, kUnionMsg, 3, "25.9"));
  EXPECT_FALSE(ReportedError(d, kUnionMsg, 4, "25.9"));
}

constexpr const char* kParamMsg =
    "virtual interface parameter values do not match the interface instance";

TEST(VirtualInterfaceParameters,
     DISABLED_AVirtualInterfaceKeepingDefaultsRefusesAnOverriddenInstance) {
  ElabFixture f;
  const auto& d = Elab(f,
                       "interface PBus #(parameter WIDTH = 8); endinterface\n"
                       "module top;\n"
                       "  PBus #(16) p16();\n"
                       "  PBus p8();\n"
                       "  virtual PBus v8;\n"
                       "  initial begin\n"
                       "    v8 = p16;\n"
                       "    v8 = p8;\n"
                       "  end\n"
                       "endmodule\n");
  EXPECT_TRUE(ReportedError(d, kParamMsg, 7, "25.9"));
  EXPECT_FALSE(ReportedError(d, kParamMsg, 8, "25.9"));
}

TEST(VirtualInterfaceParameters,
     DISABLED_ATypeParameterIsPartOfTheVirtualInterfaceType) {
  ElabFixture f;
  const auto& d = Elab(f,
                       "interface TBus #(parameter type T = int); "
                       "endinterface\n"
                       "module top;\n"
                       "  TBus #(logic) tl();\n"
                       "  TBus ti();\n"
                       "  TBus #(int) tj();\n"
                       "  virtual TBus v;\n"
                       "  initial begin\n"
                       "    v = tl;\n"
                       "    v = ti;\n"
                       "    v = tj;\n"
                       "  end\n"
                       "endmodule\n");
  EXPECT_TRUE(ReportedError(d, kParamMsg, 8, "25.9"));
  EXPECT_FALSE(ReportedError(d, kParamMsg, 9, "25.9"));
  EXPECT_FALSE(ReportedError(d, kParamMsg, 10, "25.9"));
}

TEST(VirtualInterfaceParameters, DeclarationsMatchingNoInstanceAreLegal) {
  ElabFixture f;
  ElaborateSrc(
      "interface PBus #(parameter WIDTH = 8); endinterface\n"
      "module top;\n"
      "  PBus #(16) p16();\n"
      "  virtual PBus #(35) v35;\n"
      "  virtual PBus v8;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(f.diag.Diagnostics().empty());
}

TEST(VirtualInterfaceModportAssignment, AVirtualInterfaceOfAnotherModport) {
  ElabFixture f;
  const auto& d = Elab(f,
                       "interface PBus;\n"
                       "  logic a;\n"
                       "  modport phy(input a);\n"
                       "  modport mon(input a);\n"
                       "endinterface\n"
                       "module top;\n"
                       "  virtual PBus.phy a, c;\n"
                       "  virtual PBus.mon b;\n"
                       "  initial a = b;\n"
                       "  initial a = c;\n"
                       "endmodule\n");
  EXPECT_TRUE(
      ReportedError(d, "virtual interface modports do not match", 9, "25.9"));
  EXPECT_FALSE(
      ReportedError(d, "virtual interface modports do not match", 10, "25.9"));
}

constexpr const char* kPatternSource =
    "interface vbus; logic a; endinterface\n"
    "interface other; logic a; endinterface\n"
    "module top;\n"
    "  vbus w(), x();\n"
    "  other u();\n";

constexpr const char* kPatternMsg =
    "interface instance 'u' of type 'other' is not compatible with virtual "
    "interface element type 'vbus'";

TEST(VirtualInterfaceArrayPattern,
     DISABLED_AModuleItemPatternOfAnotherInterfaceIsRefused) {
  ElabFixture f;
  const auto& d = Elab(f, std::string(kPatternSource) +
                              "  virtual vbus m[2] = '{w, u};\n"
                              "  virtual vbus k[2] = '{w, x};\n"
                              "endmodule\n");
  EXPECT_TRUE(ReportedError(d, kPatternMsg, 6, "25.9"));
  EXPECT_FALSE(ReportedError(d, "is not compatible", 7, "25.9"));
}

TEST(VirtualInterfaceArrayPattern,
     ABlockItemPatternOfAnotherInterfaceIsRefused) {
  ElabFixture f;
  const auto& d = Elab(f, std::string(kPatternSource) +
                              "  initial begin\n"
                              "    automatic virtual vbus m[2] = '{w, u};\n"
                              "    automatic virtual vbus k[2] = '{w, x};\n"
                              "  end\n"
                              "endmodule\n");
  EXPECT_TRUE(ReportedError(d, kPatternMsg, 7, "25.9"));
  EXPECT_FALSE(ReportedError(d, "is not compatible", 8, "25.9"));
}

}  // namespace
