#include <gtest/gtest.h>

#include <cstdint>
#include <format>
#include <string>
#include <string_view>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ConstExprElab, BodyParameterPromotedWithPortList) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m #(parameter int W = 8);\n"
      "  parameter int MASK = 255;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  bool found = false;
  for (auto& pd : design->top_modules[0]->params) {
    if (pd.name == "MASK") {
      found = true;
      EXPECT_TRUE(pd.is_localparam);
    }
  }
  EXPECT_TRUE(found);
}

TEST(ConstExprElab, PortListParameterDependsOnEarlier) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m #(parameter int N = 4, parameter int N2 = N * 2);\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  ASSERT_GE(design->top_modules[0]->params.size(), 2u);
  auto& p = design->top_modules[0]->params[1];
  EXPECT_EQ(p.name, "N2");
  EXPECT_TRUE(p.is_resolved);
  EXPECT_EQ(p.resolved_value, 8);
}

TEST(ConstExprElab, NonConstantParamDefaultIsReportedAndLeftUnresolved) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int P = x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "parameter 'P' value is not a constant expression",
                            2, "6.20.2"));
  EXPECT_FALSE(design->top_modules[0]->params[0].is_resolved);
}

TEST(ConstExprElab, ClassParamWithoutDefaultRequiresSpecialization) {
  ElabFixture f;
  ElaborateSrc(
      "class D #(int p);\n"
      "  int data;\n"
      "endclass\n"
      "module m;\n"
      "  D obj;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "parameterized class 'D' has no default "
                            "specialization; parameter 'p' has no default "
                            "value",
                            5, "8.25"));
}

TEST(ConstExprElab, ClassParamWithoutDefaultAcceptedWithExplicitOverride) {
  EXPECT_TRUE(
      ElabOk("class D #(int p);\n"
             "  int data;\n"
             "endclass\n"
             "module m;\n"
             "  D #(5) obj;\n"
             "endmodule\n"));
}

TEST(ConstExprElab, ClassBodyParameterElaborates) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  parameter int WIDTH = 8;\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(ConstExprElab, ClassBodyParametersChainDependencies) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  parameter int A = 1;\n"
             "  parameter int B = A + 1;\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(ConstExprElab, BodyParameterPromotedWithEmptyPortList) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m #();\n"
      "  parameter int P = 1;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  bool found = false;
  for (auto& pd : design->top_modules[0]->params) {
    if (pd.name == "P") {
      found = true;
      EXPECT_TRUE(pd.is_localparam);
    }
  }
  EXPECT_TRUE(found);
}

TEST(ConstExprElab, PortListParameterWithoutDefaultRejectsMissingOverride) {
  ElabFixture f;
  ElaborateSrc(
      "module child #(parameter int P)();\n"
      "endmodule\n"
      "module top;\n"
      "  child u0();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "parameter 'P' of 'child' has no default value and "
                            "no override at instantiation",
                            1, "6.20.1"));
}

TEST(ConstExprElab, PortListParameterWithoutDefaultAcceptedWithOverride) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int P)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.P(7)) u0();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ConstExprElab, StructParameterWithoutDefaultRejectsAMemberReadUnset) {
  ElabFixture f;
  ElaborateSrc(
      "typedef struct { int a; } s_t;\n"
      "module child #(parameter s_t P)();\n"
      "  localparam int L = P.a;\n"
      "endmodule\n"
      "module top;\n"
      "  child u0();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "parameter 'P' of 'child' has no default value and "
                            "no override at instantiation",
                            2, "6.20.1"));
}

TEST(ConstExprElab, StructParameterWithoutDefaultReadsItsOverride) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "typedef struct { int a; } s_t;\n"
      "module child #(parameter s_t P)();\n"
      "  localparam int L = P.a;\n"
      "  logic [L-1:0] v;\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.P('{a: 5})) u0();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ConstExprElab, NoDefaultParamSuppressesImplicitNestedInstantiation) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module outer;\n"
      "  module nested #(parameter int P)();\n"
      "  endmodule\n"
      "endmodule\n",
      f, "outer");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  for (const auto& child : design->top_modules[0]->children) {
    EXPECT_NE(child.module_name, "nested");
  }
}

TEST(ConstExprElab, NoDefaultParamBlocksTopElaboration) {
  ElabFixture f;
  ElaborateSrc(
      "module top #(parameter int P)();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "parameter 'P' of 'top' has no default value and "
                            "no override at instantiation",
                            1, "6.20.1"));
}

TEST(ConstExprElab, PortListMixedValueAndTypeDependencies) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module mc #(int N = 5, M = N * 16, type T = int, T x = 0)();\n"
      "endmodule\n",
      f, "mc");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const RtlirParamDecl* m = nullptr;
  const RtlirParamDecl* x = nullptr;
  for (const auto& p : design->top_modules[0]->params) {
    if (p.name == "M") m = &p;
    if (p.name == "x") x = &p;
  }
  ASSERT_NE(m, nullptr);
  EXPECT_TRUE(m->is_resolved);
  EXPECT_EQ(m->resolved_value, 80);
  ASSERT_NE(x, nullptr);
  EXPECT_TRUE(x->is_resolved);
  EXPECT_EQ(x->resolved_value, 0);
}

constexpr std::string_view kClassesWithoutDefaults =
    "class Mem #(type T, int size);\n"
    "  typedef int wt;\n"
    "  static int cnt = 3;\n"
    "  parameter int K = 2;\n"
    "  function new(int a = 0); endfunction\n"
    "  static function int f(); return 1; endfunction\n"
    "endclass\n"
    "interface class IC #(type T, int size);\n"
    "endclass\n"
    "class S #(type U = int);\n"
    "  static int n = 1;\n"
    "endclass\n";

std::string InUnit(std::string_view text) {
  return std::format("{}{}", kClassesWithoutDefaults, text);
}

std::string InModule(std::string_view items) {
  return std::format("{}module m;\n{}endmodule\n", kClassesWithoutDefaults,
                     items);
}

std::string BesidePackage(std::string_view items) {
  return std::format("package q;\n{}endpackage\nmodule m;\n{}endmodule\n",
                     kClassesWithoutDefaults, items);
}

std::string InPackage(std::string_view items) {
  return std::format("package q;\n{}{}endpackage\nmodule m;\nendmodule\n",
                     kClassesWithoutDefaults, items);
}

struct WrittenForm {
  std::string_view text;
  std::string_view unset;
};

constexpr WrittenForm kWrittenForms[] = {
    {"", "T"},
    {"#()", "T"},
    {"#(byte)", "size"},
    {"#(.T(byte))", "size"},
    {"#(.size(4))", "T"},
    {"#(.T(byte), .size())", "size"},
    {"#(byte, 4)", ""},
    {"#(.size(4), .T(byte))", ""},
};

std::string UnsetReport(std::string_view cls, const WrittenForm& form) {
  if (form.text.empty() || form.text == "#()") {
    return std::format(
        "parameterized class '{}' has no default specialization; parameter "
        "'{}' has no default value",
        cls, form.unset);
  }
  return std::format(
      "specialization of parameterized class '{}' gives no value to "
      "parameter '{}', which has no default value",
      cls, form.unset);
}

struct SpecializationSite {
  std::string_view what;
  std::string source;
  bool takes_unadorned_name = true;
  bool otherwise_clean = true;
  std::string_view cls = "Mem";
};

void ExpectEveryFormJudged(const SpecializationSite& site) {
  const uint32_t kLine = LineHolding(site.source, "@");
  ASSERT_NE(kLine, 0u) << site.what;
  for (const WrittenForm& form : kWrittenForms) {
    if (form.text.empty() && !site.takes_unadorned_name) continue;
    std::string source = site.source;
    source.replace(source.find('@'), 1, form.text);
    SCOPED_TRACE(std::format("{}: {}{}", site.what, site.cls, form.text));
    ElabFixture f;
    ElabOk(source, f);
    const auto& diags = f.diag.Diagnostics();
    if (!form.unset.empty()) {
      EXPECT_TRUE(
          ReportedError(diags, UnsetReport(site.cls, form), kLine, "8.25"));
    } else if (site.otherwise_clean) {
      EXPECT_FALSE(f.has_errors);
    } else {
      EXPECT_FALSE(ReportedError(diags, "parameterized class", kLine, "8.25"));
    }
  }
}

TEST(ClassParameterWithoutDefault, ClauseExampleGivesEveryParameterAValue) {
  EXPECT_TRUE(
      ElabOk("class Mem #(type T, int size);\n"
             "  T words[size];\n"
             "endclass\n"
             "typedef Mem#(byte, 1024) Kbyte;\n"
             "module m;\n"
             "  Kbyte k;\n"
             "endmodule\n"));
}

TEST(ClassParameterWithoutDefault, VariableOfEveryScope) {
  const SpecializationSite kSites[] = {
      {"module variable", InModule("  Mem@ v;\n")},
      {"interface variable", InUnit("interface ifc;\n"
                                    "  Mem@ v;\n"
                                    "endinterface\n"
                                    "module m;\n"
                                    "  ifc i();\n"
                                    "endmodule\n")},
      {"program variable", InUnit("program prg;\n"
                                  "  Mem@ v;\n"
                                  "endprogram\n"
                                  "module m;\n"
                                  "  prg p();\n"
                                  "endmodule\n")},
      {"checker variable", InUnit("checker chk;\n"
                                  "  Mem@ v;\n"
                                  "endchecker\n"
                                  "module m;\n"
                                  "  chk c();\n"
                                  "endmodule\n")},
      {"package variable", InPackage("  Mem@ v;\n")},
      {"compilation-unit variable", InUnit("Mem@ v;\n"
                                           "module m;\n"
                                           "endmodule\n")},
      {"generate block variable", InModule("  if (1) begin : g\n"
                                           "    Mem@ v;\n"
                                           "  end\n")},
      {"generate else branch variable", InModule("  if (0) begin : g\n"
                                                 "  end else begin : h\n"
                                                 "    Mem@ v;\n"
                                                 "  end\n")},
      {"generate case arm variable", InModule("  case (1)\n"
                                              "    1: begin : g\n"
                                              "      Mem@ v;\n"
                                              "    end\n"
                                              "    default: begin : h\n"
                                              "    end\n"
                                              "  endcase\n")},
      {"class property", InUnit("class H;\n"
                                "  Mem@ v;\n"
                                "endclass\n"
                                "module m;\n"
                                "endmodule\n")},
      {"block variable", InModule("  initial begin\n"
                                  "    Mem@ v;\n"
                                  "  end\n")},
      {"function variable", InModule("  function automatic void fn();\n"
                                     "    Mem@ v;\n"
                                     "  endfunction\n")},
      {"task variable", InModule("  task automatic tk();\n"
                                 "    Mem@ v;\n"
                                 "  endtask\n")},
      {"for loop variable",
       InModule("  initial begin\n"
                "    for (Mem@ it = null; it != null; it = null) begin end\n"
                "  end\n")},
      {"array element", InModule("  Mem@ v[2];\n")},
      {"queue element", InModule("  Mem@ v[$];\n")},
      {"associative index", InModule("  int v[Mem@];\n"), false},
      {"module variable of a class named through its package",
       BesidePackage("  q::Mem@ v;\n")},
      {"variable of a module never instantiated", InUnit("module unused;\n"
                                                         "  Mem@ v;\n"
                                                         "endmodule\n"
                                                         "module m;\n"
                                                         "endmodule\n")},
      {"variable of a generate block never built",
       InModule("  if (0) begin : g\n"
                "    Mem@ v;\n"
                "  end\n")},
      {"class named through its package", BesidePackage("  initial begin\n"
                                                        "    q::Mem@ v;\n"
                                                        "  end\n")},
  };
  for (const SpecializationSite& site : kSites) ExpectEveryFormJudged(site);
}

TEST(ClassParameterWithoutDefault, SubroutineReturnArgumentAndLocal) {
  const SpecializationSite kSites[] = {
      {"method return",
       InUnit("class H;\n"
              "  function Mem@ get(); return null; endfunction\n"
              "endclass\n"
              "module m;\n"
              "endmodule\n")},
      {"method argument", InUnit("class H;\n"
                                 "  function void put(Mem@ a); endfunction\n"
                                 "endclass\n"
                                 "module m;\n"
                                 "endmodule\n")},
      {"method variable", InUnit("class H;\n"
                                 "  function void body();\n"
                                 "    Mem@ v;\n"
                                 "  endfunction\n"
                                 "endclass\n"
                                 "module m;\n"
                                 "endmodule\n")},
      {"function return",
       InModule("  function automatic Mem@ fn(); return null; endfunction\n")},
      {"function argument",
       InModule("  function automatic void fn(Mem@ a); endfunction\n")},
  };
  for (const SpecializationSite& site : kSites) ExpectEveryFormJudged(site);
}

TEST(ClassParameterWithoutDefault, TypedefOfEveryScope) {
  const SpecializationSite kSites[] = {
      {"compilation-unit typedef", InUnit("typedef Mem@ t;\n"
                                          "module m;\n"
                                          "endmodule\n")},
      {"module typedef", InModule("  typedef Mem@ t;\n")},
      {"package typedef", InPackage("  typedef Mem@ t;\n")},
      {"class typedef", InUnit("class H;\n"
                               "  typedef Mem@ t;\n"
                               "endclass\n"
                               "module m;\n"
                               "endmodule\n")},
      {"typedef of a class named through its package",
       BesidePackage("  typedef q::Mem@ t;\n")},
  };
  for (const SpecializationSite& site : kSites) ExpectEveryFormJudged(site);
}

TEST(ClassParameterWithoutDefault, ExtendedAndImplementedClass) {
  const SpecializationSite kSites[] = {
      {"extends", InUnit("class E extends Mem@;\n"
                         "endclass\n"
                         "module m;\n"
                         "endmodule\n")},
      {"extends with constructor arguments", InUnit("class E extends Mem@(5);\n"
                                                    "endclass\n"
                                                    "module m;\n"
                                                    "endmodule\n")},
      {"implements",
       InUnit("class F implements IC@;\n"
              "endclass\n"
              "module m;\n"
              "endmodule\n"),
       true, true, "IC"},
      {"interface class extends",
       InUnit("interface class G extends IC@;\n"
              "endclass\n"
              "module m;\n"
              "endmodule\n"),
       true, true, "IC"},
  };
  for (const SpecializationSite& site : kSites) ExpectEveryFormJudged(site);
}

TEST(ClassParameterWithoutDefault, TypeWrittenInsideAnotherDeclaration) {
  const SpecializationSite kSites[] = {
      {"argument of another specialization", InModule("  S#(Mem@) v;\n")},
      {"argument of a property's specialization", InUnit("class H;\n"
                                                         "  S#(Mem@) v;\n"
                                                         "endclass\n"
                                                         "module m;\n"
                                                         "endmodule\n")},
      {"structure member", InModule("  typedef struct { Mem@ h; } st_t;\n")},
      {"port", InUnit("module child(input Mem@ h);\n"
                      "endmodule\n"
                      "module m;\n"
                      "  child c(.h(null));\n"
                      "endmodule\n")},
      {"module type parameter default",
       InUnit("module m #(parameter type PT = Mem@);\n"
              "endmodule\n")},
      {"class type parameter default", InUnit("class X #(type PT = Mem@);\n"
                                              "endclass\n"
                                              "module m;\n"
                                              "endmodule\n")},
      {"instance type parameter override",
       InUnit("module child #(parameter type PT = int);\n"
              "endmodule\n"
              "module m;\n"
              "  child #(.PT(Mem@)) c();\n"
              "endmodule\n")},
      {"member of a nested structure",
       InModule("  typedef struct { struct { Mem@ h; } inner; } st_t;\n")},
      {"module body type parameter", InModule("  parameter type PT = Mem@;\n")},
  };
  for (const SpecializationSite& site : kSites) ExpectEveryFormJudged(site);
}

TEST(ClassParameterWithoutDefault, ScopePrefixOfAType) {
  const SpecializationSite kSites[] = {
      {"compilation-unit typedef",
       InUnit("typedef Mem@::wt t;\n"
              "module m;\n"
              "endmodule\n"),
       false},
      {"module typedef", InModule("  typedef Mem@::wt t;\n"), false},
      {"module variable", InModule("  Mem@::wt v;\n"), false},
      {"class property",
       InUnit("class H;\n"
              "  Mem@::wt v;\n"
              "endclass\n"
              "module m;\n"
              "endmodule\n"),
       false},
      {"package variable", InPackage("  Mem@::wt v;\n"), false},
      {"block variable",
       InModule("  initial begin\n"
                "    Mem@::wt v;\n"
                "  end\n"),
       false},
  };
  for (const SpecializationSite& site : kSites) ExpectEveryFormJudged(site);
}

TEST(ClassParameterWithoutDefault, ScopePrefixInADeclarationsExpression) {
  const SpecializationSite kSites[] = {
      {"module variable initializer", InModule("  int x = Mem@::cnt;\n"),
       false},
      {"the class's own parameter", InModule("  int x = Mem@::size;\n"), false},
      {"compilation-unit variable initializer",
       InUnit("int x = Mem@::cnt;\n"
              "module m;\n"
              "endmodule\n"),
       false},
      {"interface variable initializer",
       InUnit("interface ifc;\n"
              "  int x = Mem@::cnt;\n"
              "endinterface\n"
              "module m;\n"
              "  ifc i();\n"
              "endmodule\n"),
       false},
      {"generate block variable initializer",
       InModule("  if (1) begin : g\n"
                "    int x = Mem@::cnt;\n"
                "  end\n"),
       false},
      {"class property initializer",
       InUnit("class H;\n"
              "  int v = Mem@::cnt;\n"
              "endclass\n"
              "module m;\n"
              "endmodule\n"),
       false},
      {"localparam value", InModule("  localparam int L = Mem@::K;\n"), false,
       false},
      {"parameter port default",
       InUnit("module m #(parameter int PV = Mem@::K);\n"
              "endmodule\n"),
       false, false},
      {"packed dimension", InModule("  logic [Mem@::K:0] v;\n"), false},
      {"unpacked dimension", InModule("  int v[Mem@::K];\n"), false},
      {"continuous assignment",
       InModule("  wire [31:0] w;\n"
                "  assign w = Mem@::K;\n"),
       false},
      {"generate condition",
       InModule("  if (Mem@::K > 1) begin : g\n"
                "  end\n"),
       false},
      {"instance parameter override",
       InUnit("module child #(parameter int P = 1);\n"
              "endmodule\n"
              "module m;\n"
              "  child #(.P(Mem@::K)) c();\n"
              "endmodule\n"),
       false},
      {"argument default",
       InModule("  function automatic int fn(int a = Mem@::K);\n"
                "    return a;\n"
                "  endfunction\n"),
       false},
      {"constraint",
       InUnit("class H;\n"
              "  rand int r;\n"
              "  constraint c { r < Mem@::K; }\n"
              "endclass\n"
              "module m;\n"
              "endmodule\n"),
       false},
      {"argument of a specialized scope prefix",
       InModule("  int x = S#(Mem@)::n;\n")},
  };
  for (const SpecializationSite& site : kSites) ExpectEveryFormJudged(site);
}

TEST(ClassParameterWithoutDefault, ScopePrefixInAStatement) {
  const SpecializationSite kSites[] = {
      {"initial block assignment",
       InModule("  int x;\n"
                "  initial begin\n"
                "    x = Mem@::cnt;\n"
                "  end\n"),
       false},
      {"program statement",
       InUnit("program prg;\n"
              "  int x;\n"
              "  initial x = Mem@::cnt;\n"
              "endprogram\n"
              "module m;\n"
              "  prg p();\n"
              "endmodule\n"),
       false},
      {"method body",
       InUnit("class H;\n"
              "  function int g();\n"
              "    return Mem@::cnt;\n"
              "  endfunction\n"
              "endclass\n"
              "module m;\n"
              "endmodule\n"),
       false},
      {"package function",
       InPackage("  function automatic int pf();\n"
                 "    return Mem@::cnt;\n"
                 "  endfunction\n"),
       false},
      {"static method call",
       InModule("  int x;\n"
                "  initial x = Mem@::f();\n"),
       false},
      {"typed constructor call",
       InModule("  Mem#(byte, 4) h;\n"
                "  initial h = Mem@::new;\n"),
       false},
      {"concatenation operand",
       InModule("  int x;\n"
                "  initial x = {Mem@::cnt, 1'b0};\n"),
       false},
      {"block variable initializer",
       InModule("  initial begin\n"
                "    automatic int y = Mem@::cnt;\n"
                "  end\n"),
       false},
      {"call argument",
       InModule("  function automatic int fn(int a); return a; endfunction\n"
                "  int x;\n"
                "  initial x = fn(Mem@::cnt);\n"),
       false},
      {"if condition",
       InModule("  int x;\n"
                "  initial if (Mem@::cnt > 1) x = 1;\n"),
       false},
  };
  for (const SpecializationSite& site : kSites) ExpectEveryFormJudged(site);
}

TEST(ClassParameterWithoutDefault,
     ParameterAfterADefaultedOneStillNeedsAValue) {
  ElabFixture f;
  ElabOk(
      "class E #(int a = 1, int b);\n"
      "endclass\n"
      "module m;\n"
      "  E#(5) x;\n"
      "  E#(.a(5)) y;\n"
      "  E#(.b(2)) ok_named;\n"
      "  E#(5, 6) ok_ordered;\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (const uint32_t kLine : {4u, 5u}) {
    EXPECT_TRUE(ReportedError(diags,
                              "specialization of parameterized class 'E' "
                              "gives no value to parameter 'b', which has no "
                              "default value",
                              kLine, "8.25"))
        << kLine;
  }
  for (const uint32_t kLine : {6u, 7u}) {
    EXPECT_FALSE(ReportedError(diags, "parameterized class", kLine, "8.25"))
        << kLine;
  }
}

TEST(ClassParameterWithoutDefault, DefaultedParameterMayBeLeftOut) {
  EXPECT_TRUE(
      ElabOk("class C #(int a, int b = 2);\n"
             "  static int m = 1;\n"
             "  typedef int wt;\n"
             "endclass\n"
             "class All #(int p = 1);\n"
             "  static int m = 1;\n"
             "endclass\n"
             "package pk;\n"
             "  typedef int word_t;\n"
             "endpackage\n"
             "module m;\n"
             "  pk::word_t w;\n"
             "  C#(5) c;\n"
             "  C#(.a(5)) named;\n"
             "  C#(5)::wt v;\n"
             "  All#() all;\n"
             "  int x = C#(5)::m + All#()::m;\n"
             "endmodule\n"));
}

TEST(ClassParameterWithoutDefault, LocalParameterTakesNoOrderedArgument) {
  ElabFixture f;
  ElabOk(
      "class LP #(localparam int half = 2, parameter int b);\n"
      "endclass\n"
      "class Three #(int a = 1, int b, int c = 3);\n"
      "endclass\n"
      "module m;\n"
      "  LP#(5) given;\n"
      "  LP#() left;\n"
      "  Three#(.a(1), .c(2)) skipped;\n"
      "  Three#(.c(2), .b(4)) named;\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_FALSE(ReportedError(diags, "parameterized class", 6, "8.25"));
  EXPECT_TRUE(ReportedError(diags,
                            "parameterized class 'LP' has no default "
                            "specialization; parameter 'b' has no default "
                            "value",
                            7, "8.25"));
  EXPECT_TRUE(ReportedError(diags,
                            "specialization of parameterized class 'Three' "
                            "gives no value to parameter 'b', which has no "
                            "default value",
                            8, "8.25"));
  EXPECT_FALSE(ReportedError(diags, "parameterized class", 9, "8.25"));
}

TEST(ClassParameterWithoutDefault, NestedClassBehindASpecializedScope) {
  ElabFixture f;
  ElabOk(
      "class Outer #(int a);\n"
      "  class Inner #(int b = 1);\n"
      "  endclass\n"
      "  class Needy #(int c);\n"
      "  endclass\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    Outer#()::Inner#(3) outer_unset;\n"
      "    Outer#(1)::Inner#(3) both_given;\n"
      "    Outer#(1)::Inner inner_defaulted;\n"
      "    Outer#(1)::Needy inner_unadorned;\n"
      "    Outer#(1)::Needy#() inner_empty;\n"
      "    Outer#(1)::Needy#(2) inner_given;\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(diags,
                            "parameterized class 'Outer' has no default "
                            "specialization; parameter 'a' has no default "
                            "value",
                            9, "8.25"));
  for (const uint32_t kLine : {12u, 13u}) {
    EXPECT_TRUE(ReportedError(diags,
                              "parameterized class 'Needy' has no default "
                              "specialization; parameter 'c' has no default "
                              "value",
                              kLine, "8.25"))
        << kLine;
  }
  for (const uint32_t kLine : {10u, 11u, 14u}) {
    EXPECT_FALSE(ReportedError(diags, "parameterized class", kLine, "8.25"))
        << kLine;
  }
}

TEST(ClassParameterWithoutDefault, BaseNamedByATypeParameter) {
  ElabFixture f;
  ElabOk(InUnit("class ByDefault #(type P = Mem#(byte, 4)) extends P;\n"
                "endclass\n"
                "class Unset #(type P = Mem#(byte)) extends P;\n"
                "endclass\n"
                "module m;\n"
                "endmodule\n"),
         f);
  const auto& diags = f.diag.Diagnostics();
  const std::string kSource = InUnit(
      "class ByDefault #(type P = Mem#(byte, 4))"
      " extends P;\n"
      "endclass\n"
      "class Unset #(type P = Mem#(byte)) "
      "extends P;\n");
  EXPECT_FALSE(ReportedError(diags, "parameterized class",
                             LineHolding(kSource, "class ByDefault"), "8.25"));
  EXPECT_TRUE(ReportedError(diags,
                            "specialization of parameterized class 'Mem' "
                            "gives no value to parameter 'size', which has no "
                            "default value",
                            LineHolding(kSource, "class Unset"), "8.25"));
}

}  // namespace
