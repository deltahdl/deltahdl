#include <gtest/gtest.h>

#include "common/types.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"

using namespace delta;

namespace {

TEST(TypeDeclElaboration, DataDeclVariableElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic [7:0] data;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& v : mod->variables) {
    if (v.name == "data") {
      EXPECT_EQ(v.width, 8u);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(TypeDeclElaboration, DataDeclMultipleVariables) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic a, b, c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  int count = 0;
  for (const auto& v : mod->variables) {
    if (v.name == "a" || v.name == "b" || v.name == "c") count++;
  }
  EXPECT_GE(count, 3);
}

TEST(TypeDeclElaboration, DataDeclVarPrefix) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  var logic x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& v : mod->variables) {
    if (v.name == "x") found = true;
  }
  EXPECT_TRUE(found);
}

TEST(TypeDeclElaboration, NetDeclWireElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire [7:0] bus;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& n : mod->nets) {
    if (n.name == "bus") {
      EXPECT_EQ(n.width, 8u);
      EXPECT_EQ(n.net_type, NetType::kWire);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(TypeDeclElaboration, NetDeclTriElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  tri t;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& n : mod->nets) {
    if (n.name == "t") {
      EXPECT_EQ(n.net_type, NetType::kTri);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(TypeDeclElaboration, NetDeclMultipleNets) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b, c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  int count = 0;
  for (const auto& n : mod->nets) {
    if (n.name == "a" || n.name == "b" || n.name == "c") count++;
  }
  EXPECT_GE(count, 3);
}

TEST(TypeDeclElaboration, TypedefEnumElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  EXPECT_TRUE(mod->enum_types.count("color_t"));
  EXPECT_EQ(mod->enum_types.at("color_t").size(), 3u);
}

TEST(TypeDeclElaboration, TypedefStructRegistersType) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TypeDeclElaboration, TypedefDataTypeUsable) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  typedef logic [7:0] byte_t;\n"
      "  byte_t val;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& v : mod->variables) {
    if (v.name == "val") {
      EXPECT_EQ(v.width, 8u);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(TypeDeclElaboration, GenvarDeclElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  genvar i;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TypeDeclElaboration, PackageImportElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "package pkg; endpackage\n"
      "module m;\n"
      "  import pkg::*;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TypeDeclElaboration, NettypeDeclElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  nettype real real_net;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TypeDeclElaboration, PackageExportElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "package src; endpackage\n"
      "package dst;\n"
      "  import src::*;\n"
      "  export src::*;\n"
      "endpackage\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TypeDeclElaboration, NetDeclInterconnectElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  interconnect [3:0] bus;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TypeDeclElaboration, ErrorRedeclarationDetected) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic x;\n"
      "  logic x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  // A variable redeclaring a variable is the case §6.5's closing sentence
  // names, so the report carries §6.5 rather than §23.9's general rule.
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'x'", 3, "6.5"));
}

TEST(TypeDeclElaboration, ErrorVectoredOrScalaredWithoutPackedDim) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire vectored w;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "vectored or scalared requires at least one packed "
                            "dimension",
                            2, "6.9.2"));
}

TEST(TypeDeclElaboration, TriregChargeStrengthAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  trireg (large) cap;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// A.2.1.3 with A.2.2.1: a with clause's class_scope names the class through
// every name it writes, a package first or a class whose nested classes the
// later names pick out (§8.23), and a specialization's parameter values pick
// no other class. Each class reached here declares a static `res`, which
// §6.6.7 admits, while the top-level classes of the same last name declare a
// non-static one, which it rejects; a lookup by the last name alone reaches
// those and reports them (#7592).
constexpr const char* kNettypeScopeChains =
    "class C;\n"
    "  function real res(input real d[]); return 0.0; endfunction\n"
    "endclass\n"
    "class Inner;\n"
    "  function real res(input real d[]); return 0.0; endfunction\n"
    "endclass\n"
    "package P;\n"
    "  class C #(int W = 1);\n"
    "    static function real res(input real d[]); return 0.0; endfunction\n"
    "  endclass\n"
    "  class Outer;\n"
    "    class Inner;\n"
    "      static function real res(input real d[]);\n"
    "        return 0.0;\n"
    "      endfunction\n"
    "    endclass\n"
    "  endclass\n"
    "endpackage\n"
    "class Outer;\n"
    "  class Inner;\n"
    "    static function real res(input real d[]); return 0.0; endfunction\n"
    "  endclass\n"
    "endclass\n"
    "module m;\n"
    "  nettype real n1 with P::C#(8)::res;\n"
    "  nettype real n2 with P::C::res;\n"
    "  nettype real n3 with Outer::Inner::res;\n"
    "  nettype real n4 with P::Outer::Inner::res;\n"
    "  n3 w;\n"
    "endmodule\n";

TEST(TypeDeclElaboration, NettypeResolutionFunctionFoundThroughAClassChain) {
  ElabFixture f;
  auto* design = Elaborate(kNettypeScopeChains, f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const RtlirNet* net = FindNet(design, "m", "w");
  ASSERT_NE(net, nullptr);
  EXPECT_EQ(net->resolve_func, "Outer::Inner::res");
}

// A.2.2.1's package_scope `$unit ::` names the compilation unit, so
// `$unit::ufn` is the unit's function and not the module's own `ufn`, whose
// second argument §6.6.7 rejects, and `$unit::U` is the unit's class U, by its
// own name or a unit typedef's: a class C only a package declares is not
// reached through `$unit::C`.
TEST(TypeDeclElaboration, NettypeResolutionFunctionFoundThroughUnitScope) {
  ElabFixture f;
  auto* design = Elaborate(
      "function real ufn(input real d[]); return 0.0; endfunction\n"
      "class U;\n"
      "  static function real res(input real d[]); return 0.0; endfunction\n"
      "endclass\n"
      "typedef U UT;\n"
      "module m;\n"
      "  function real ufn(input real d[], input int k); return 0.0; "
      "endfunction\n"
      "  nettype real n1 with $unit::ufn;\n"
      "  nettype real n2 with $unit::U::res;\n"
      "  nettype real n3 with $unit::UT::res;\n"
      "  n1 w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const RtlirNet* net = FindNet(design, "m", "w");
  ASSERT_NE(net, nullptr);
  EXPECT_EQ(net->resolve_func, "$unit::ufn");
}

// §6.6.7's two reports on a scope keep the whole chain: one that reaches no
// class, here a package declaring no Nope and a unit declaring no class C
// although P does, and one reaching a class that declares no such function.
TEST(TypeDeclElaboration, NettypeResolutionClassChainReportsNameTheChain) {
  ElabFixture f;
  Elaborate(
      "package P;\n"
      "  class C;\n"
      "    static function real res(input real d[]); return 0.0; endfunction\n"
      "  endclass\n"
      "endpackage\n"
      "module m;\n"
      "  nettype real n1 with P::Nope::res;\n"
      "  nettype real n2 with $unit::C::res;\n"
      "  nettype real n3 with P::C#()::missing;\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(diags,
                            "resolution function of user-defined nettype 'n1' "
                            "names unknown package or class 'P::Nope'",
                            7, "6.6.7"));
  EXPECT_TRUE(ReportedError(diags,
                            "resolution function of user-defined nettype 'n2' "
                            "names unknown package or class '$unit::C'",
                            8, "6.6.7"));
  EXPECT_TRUE(ReportedError(diags,
                            "resolution function 'P::C::missing' of "
                            "user-defined nettype 'n3' does not exist",
                            9, "6.6.7"));
}

// A.2.1.3 with A.2.2.1: a qualified data declaration of a package's type
// declares a variable of that type, four bits from P::T where the module's own
// T is eight (#7603).
TEST(TypeDeclElaboration, AQualifiedDeclarationTakesThePackagesType) {
  ElabFixture f;
  auto* design = Elaborate(
      "package P;\n"
      "  typedef logic [3:0] T;\n"
      "endpackage\n"
      "module m;\n"
      "  typedef logic [7:0] T;\n"
      "  var P::T a;\n"
      "  const P::T b = 4'hA;\n"
      "  static P::T c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const char* const kNames[] = {"a", "b", "c"};
  for (const char* name : kNames) {
    const RtlirVariable* v = FindVar(design, "m", name);
    ASSERT_NE(v, nullptr) << name;
    EXPECT_EQ(v->width, 4u) << name;
  }
}

// §6.6.7: a nettype may declare only a net, and `var` opens a data
// declaration, so a package's nettype named after it is reported under the
// name the package gives it.
TEST(TypeDeclElaboration, AVarDeclarationOfAPackagesNettypeIsReported) {
  ElabFixture f;
  Elaborate(
      "package P;\n"
      "  nettype logic [3:0] nt;\n"
      "endpackage\n"
      "module m;\n"
      "  var P::nt v;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "nettype 'P::nt' may declare only a net, and is "
                            "named here as the type of variable 'v'",
                            5, "6.6.7"));
}

}  // namespace
