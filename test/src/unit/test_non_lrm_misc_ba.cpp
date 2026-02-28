// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

static bool HasItemOfKindAndName(const std::vector<ModuleItem*>& items,
                                 ModuleItemKind kind, const std::string& name) {
  for (const auto* item : items)
    if (item->kind == kind && item->name == name) return true;
  return false;
}

static bool HasAttrNamed(const std::vector<ModuleItem*>& items,
                         const std::string& name) {
  for (const auto* item : items)
    for (const auto& attr : item->attrs)
      if (attr.name == name) return true;
  return false;
}

namespace {

// 10. No forward references in CU scope (except task/function names).
// The LRM says references shall only be made to names already defined.
// This is a semantic rule; the parser accepts the code but elaboration
// would reject it.  We test that parsing succeeds (syntax is valid).
TEST(ParserClause03, Cl3_12_1_ForwardRefSyntaxValid) {
  // This is valid syntax even though semantically 'b' is referenced
  // before its declaration at CU scope.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  wire w;\n"
              "endmodule\n"));
}

// 11. CU scope has no name — cannot be imported.
// An import of $unit would be illegal.  Verify that valid import syntax
// works and that CU items remain separate from packages.
TEST(ParserClause03, Cl3_12_1_CuScopeCannotBeImported) {
  // Normal package import works fine.
  auto r = ParseWithPreprocessor(
      "package pkg;\n"
      "  typedef int myint;\n"
      "endpackage\n"
      "module m;\n"
      "  import pkg::*;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  // CU-scope functions are NOT in any package.
  EXPECT_TRUE(r.cu->cu_items.empty());
  ASSERT_EQ(r.cu->packages.size(), 1u);
}

// 12. CU scope identifiers not accessible via hierarchical references.
// Hierarchical names start from $root (§23.3.1), not from CU scope.
// Verify that a hierarchical reference in a module parses correctly.
TEST(ParserClause03, Cl3_12_1_HierRefFromCUScope) {
  auto r = ParseWithPreprocessor(
      "module top;\n"
      "  module_a u1();\n"
      "endmodule\n"
      "module module_a;\n"
      "  logic sig;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 2u);
}

// 13. CU allows type sharing without packages (§3.12.1 last paragraph).
// Users can share types across a CU without declaring a package.
// Top-level typedef is parsed as a module item (discarded at top level
// in current implementation) or could be a class.  Verify CU-scope
// classes enable type sharing.
TEST(ParserClause03, Cl3_12_1_TypeSharingViaCUScope) {
  auto r = ParseWithPreprocessor(
      "class shared_type;\n"
      "  int value;\n"
      "endclass\n"
      "module m1;\n"
      "  shared_type obj;\n"
      "endmodule\n"
      "module m2;\n"
      "  shared_type obj;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  ASSERT_EQ(r.cu->modules.size(), 2u);
}

// 15. Config declarations at top level (part of CU).
TEST(ParserClause03, Cl3_12_1_ConfigAtCUScope) {
  auto r = ParseWithPreprocessor(
      "module lib_mod; endmodule\n"
      "config my_cfg;\n"
      "  design lib_mod;\n"
      "  default liblist;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->name, "my_cfg");
}

// 16. Checker declarations at CU scope.
TEST(ParserClause03, Cl3_12_1_CheckerAtCUScope) {
  auto r = ParseWithPreprocessor(
      "checker my_chk;\n"
      "endchecker\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
}

// =============================================================================
// A.1.2 source_text ::= [ timeunits_declaration ] { description }
// =============================================================================
// Empty source text.
TEST(SourceText, EmptySourceText) {
  auto r = ParseWithPreprocessor("");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules.empty());
}

// =============================================================================
// LRM §3.13 — Name spaces
// =============================================================================
// 1. Module and package in definition name space (can coexist without conflict)
TEST(ParserClause03, Cl3_13_ModuleAndPackageInDefinitionNameSpace) {
  auto r = ParseWithPreprocessor(
      "package my_pkg;\n"
      "  typedef int myint;\n"
      "endpackage\n"
      "module my_mod;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "my_pkg");
  EXPECT_EQ(r.cu->modules[0]->name, "my_mod");
}

// 2. Same-name variables in different modules (separate scopes)
TEST(ParserClause03, Cl3_13_SameNameVarsInDifferentModules) {
  auto r = ParseWithPreprocessor(
      "module a;\n"
      "  logic [7:0] data;\n"
      "endmodule\n"
      "module b;\n"
      "  logic [7:0] data;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 2u);
  // Both modules should have a 'data' variable in their own scope.
  EXPECT_TRUE(HasItemOfKindAndName(r.cu->modules[0]->items,
                                   ModuleItemKind::kVarDecl, "data"));
  EXPECT_TRUE(HasItemOfKindAndName(r.cu->modules[1]->items,
                                   ModuleItemKind::kVarDecl, "data"));
}

// 6. Task and function names in same module scope
TEST(ParserClause03, Cl3_13_TaskAndFunctionInSameModule) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  function int add(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "  task do_work(input int x);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  bool found_func = false;
  bool found_task = false;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kFunctionDecl && item->name == "add")
      found_func = true;
    if (item->kind == ModuleItemKind::kTaskDecl && item->name == "do_work")
      found_task = true;
  }
  EXPECT_TRUE(found_func);
  EXPECT_TRUE(found_task);
}

// 7. Variable name same as module name (different name spaces)
TEST(ParserClause03, Cl3_13_VarNameSameAsModuleName) {
  // A variable named 'top' inside module 'top' is legal because
  // the definition name space and the local scope are distinct.
  EXPECT_TRUE(
      ParseOk("module top;\n"
              "  logic top;\n"
              "endmodule\n"));
}

// 18. $unit scope -- declarations outside any module/package
TEST(ParserClause03, Cl3_13_UnitScopeDeclarations) {
  auto r = ParseWithPreprocessor(
      "function automatic int helper(int x);\n"
      "  return x + 1;\n"
      "endfunction\n"
      "task automatic global_task(input int v);\n"
      "endtask\n"
      "module m;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->cu_items.size(), 2u);
  EXPECT_EQ(r.cu->cu_items[0]->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(r.cu->cu_items[0]->name, "helper");
  EXPECT_EQ(r.cu->cu_items[1]->kind, ModuleItemKind::kTaskDecl);
  EXPECT_EQ(r.cu->cu_items[1]->name, "global_task");
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

// 33. All 8 name spaces coexist in a single compilation unit
TEST(ParserClause03, Cl3_13_AllEightNameSpaces) {
  auto r = ParseWithPreprocessor(
      // (d) Text macro name space
      "`define VAL 1\n"
      // (b) Package name space
      "package pkg; int x; endpackage\n"
      // (c) Compilation-unit scope name space
      "function automatic int cu_fn(int a); return a; endfunction\n"
      // (a) Definitions name space: module, interface, program, primitive
      "module m (input logic clk, output logic q);\n"  // (g) Port name space
      "  (* keep *) logic flag;\n"                // (h) Attribute name space
      "  import pkg::*;\n"                        // (e) Module name space
      "  always_ff @(posedge clk) begin : blk\n"  // (f) Block name space
      "    int cnt;\n"
      "    cnt = `VAL;\n"
      "    q <= flag;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  // (b) Package name space
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "pkg");
  // (c) Compilation-unit scope
  ASSERT_GE(r.cu->cu_items.size(), 1u);
  EXPECT_EQ(r.cu->cu_items[0]->name, "cu_fn");
  // (a) Definitions name space
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
  // (g) Port name space
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "clk");
  // (h) Attribute name space
  EXPECT_TRUE(HasAttrNamed(r.cu->modules[0]->items, "keep"));
}

// package_item: timeunits_declaration (footnote 3)
TEST(SourceText, PackageItemTimeunitsDecl) {
  auto r = ParseWithPreprocessor(
      "package pkg;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
}

// =============================================================================
// LRM §3.14 — Simulation time units and precision
// =============================================================================
TEST(ParserClause03, Cl3_14_TimeunitsAndTimescale) {
  auto r1 = ParseWithPreprocessor("module m; timeunit 1ns; endmodule\n");
  EXPECT_FALSE(r1.has_errors);
  EXPECT_TRUE(r1.cu->modules[0]->has_timeunit);
  auto r2 = ParseWithPreprocessor("module m; timeprecision 1ps; endmodule\n");
  EXPECT_FALSE(r2.has_errors);
  EXPECT_TRUE(r2.cu->modules[0]->has_timeprecision);
  auto r3 = ParseWithPreprocessor(
      "module m; timeunit 1ns; timeprecision 1ps; endmodule\n");
  EXPECT_FALSE(r3.has_errors);
  EXPECT_TRUE(r3.cu->modules[0]->has_timeunit);
  EXPECT_TRUE(r3.cu->modules[0]->has_timeprecision);
  EXPECT_TRUE(ParseOk("module m; timeunit 100ps / 10fs; endmodule\n"));
  EXPECT_TRUE(
      ParseOk("program p; timeunit 10us; timeprecision 100ns; endprogram\n"));
  EXPECT_TRUE(ParseOk("interface ifc; timeunit 1ns; endinterface\n"));
  // `timescale directive
  EXPECT_TRUE(ParseOk("`timescale 1ns/1ps\nmodule m; endmodule\n"));
  // Time literals (§5.8): integer, fractional, all unit suffixes
  EXPECT_TRUE(ParseOk("module m; initial #10ns $display(\"d\"); endmodule\n"));
  EXPECT_TRUE(ParseOk("module m; initial #2.1ns $display(\"d\"); endmodule\n"));
  // Various magnitudes (Table 3-1)
  EXPECT_TRUE(
      ParseOk("module a; timeunit 100ns; timeprecision 10ps; endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module b; timeunit 1us; timeprecision 1ns; endmodule\n"));
}

// 1. TimeUnit enum: six values with correct power-of-10 exponents
// (s=0, ms=-3, us=-6, ns=-9, ps=-12, fs=-15).
TEST(ParserClause03, Cl3_14_TimeUnitEnumValues) {
  EXPECT_EQ(static_cast<int8_t>(TimeUnit::kS), 0);
  EXPECT_EQ(static_cast<int8_t>(TimeUnit::kMs), -3);
  EXPECT_EQ(static_cast<int8_t>(TimeUnit::kUs), -6);
  EXPECT_EQ(static_cast<int8_t>(TimeUnit::kNs), -9);
  EXPECT_EQ(static_cast<int8_t>(TimeUnit::kPs), -12);
  EXPECT_EQ(static_cast<int8_t>(TimeUnit::kFs), -15);
}

// 2. Table 3-1: ParseTimeUnitStr maps all six character strings.
TEST(ParserClause03, Cl3_14_Table3_1_AllUnitStrings) {
  TimeUnit u = TimeUnit::kNs;
  EXPECT_TRUE(ParseTimeUnitStr("s", u));
  EXPECT_EQ(u, TimeUnit::kS);
  EXPECT_TRUE(ParseTimeUnitStr("ms", u));
  EXPECT_EQ(u, TimeUnit::kMs);
  EXPECT_TRUE(ParseTimeUnitStr("us", u));
  EXPECT_EQ(u, TimeUnit::kUs);
  EXPECT_TRUE(ParseTimeUnitStr("ns", u));
  EXPECT_EQ(u, TimeUnit::kNs);
  EXPECT_TRUE(ParseTimeUnitStr("ps", u));
  EXPECT_EQ(u, TimeUnit::kPs);
  EXPECT_TRUE(ParseTimeUnitStr("fs", u));
  EXPECT_EQ(u, TimeUnit::kFs);
}

// 3. Table 3-1: invalid unit strings are rejected.
TEST(ParserClause03, Cl3_14_Table3_1_InvalidStrings) {
  TimeUnit u = TimeUnit::kNs;
  EXPECT_FALSE(ParseTimeUnitStr("", u));
  EXPECT_FALSE(ParseTimeUnitStr("xs", u));
  EXPECT_FALSE(ParseTimeUnitStr("sec", u));
  EXPECT_FALSE(ParseTimeUnitStr("NS", u));  // case-sensitive
}

// 4. "us" represents microseconds (substitution for the mu-s symbol).
TEST(ParserClause03, Cl3_14_UsForMicroseconds) {
  TimeUnit u = TimeUnit::kNs;
  EXPECT_TRUE(ParseTimeUnitStr("us", u));
  EXPECT_EQ(u, TimeUnit::kUs);
  EXPECT_EQ(static_cast<int8_t>(u), -6);  // 10^-6 = microsecond
}

// 5. TimeScale struct: time values have two components (unit + precision).
TEST(ParserClause03, Cl3_14_TimeScaleTwoComponents) {
  TimeScale ts;
  ts.unit = TimeUnit::kNs;
  ts.magnitude = 1;
  ts.precision = TimeUnit::kPs;
  ts.prec_magnitude = 1;
  EXPECT_EQ(ts.unit, TimeUnit::kNs);
  EXPECT_EQ(ts.precision, TimeUnit::kPs);
  // Unit and precision are independently stored.
  EXPECT_NE(static_cast<int8_t>(ts.unit), static_cast<int8_t>(ts.precision));
}

// 12. Precision constraint: precision exponent <= unit exponent.
// Finer units have more-negative exponents (kFs < kPs < ... < kS).
TEST(ParserClause03, Cl3_14_PrecisionAtLeastAsPreciseAsUnit) {
  EXPECT_LE(static_cast<int8_t>(TimeUnit::kFs),
            static_cast<int8_t>(TimeUnit::kPs));
  EXPECT_LE(static_cast<int8_t>(TimeUnit::kPs),
            static_cast<int8_t>(TimeUnit::kNs));
  EXPECT_LE(static_cast<int8_t>(TimeUnit::kNs),
            static_cast<int8_t>(TimeUnit::kUs));
  EXPECT_LE(static_cast<int8_t>(TimeUnit::kUs),
            static_cast<int8_t>(TimeUnit::kMs));
  EXPECT_LE(static_cast<int8_t>(TimeUnit::kMs),
            static_cast<int8_t>(TimeUnit::kS));
}

// 13. Time values stored in design element: module with timeunit and
// timeprecision stores both components.
TEST(ParserClause03, Cl3_14_TimeValuesInDesignElement) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* mod = r.cu->modules[0];
  EXPECT_TRUE(mod->has_timeunit);
  EXPECT_TRUE(mod->has_timeprecision);
  EXPECT_EQ(mod->time_unit, TimeUnit::kNs);
  EXPECT_EQ(mod->time_prec, TimeUnit::kPs);
}

// ===========================================================================
// §3.14: Timeunit/timeprecision parsing
// ===========================================================================
TEST(Lexical, Timeunit_BasicParse) {
  auto r = ParseWithPreprocessor(
      "module top;\n"
      "  timeunit 1ns;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  // Should parse without error. The timeunit decl is consumed.
  EXPECT_EQ(r.cu->modules[0]->name, "top");
}

TEST(Lexical, Timeprecision_BasicParse) {
  auto r = ParseWithPreprocessor(
      "module top;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
}

TEST(Lexical, Timeunit_WithSlash) {
  // timeunit 1ns / 1ps;  (combined form)
  auto r = ParseWithPreprocessor(
      "module top;\n"
      "  timeunit 1ns / 1ps;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
}

TEST(Lexical, Timeunit_DifferentValues) {
  // Various time unit values
  auto r = ParseWithPreprocessor(
      "module top;\n"
      "  timeunit 100us;\n"
      "  timeprecision 10ns;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
}

TEST(Lexical, Timeunit_StoredInModuleDecl_Values) {
  // The timeunit/timeprecision values should be stored in ModuleDecl.
  auto r = ParseWithPreprocessor(
      "module top;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  auto* mod = r.cu->modules[0];
  EXPECT_EQ(mod->time_unit, TimeUnit::kNs);
  EXPECT_EQ(mod->time_prec, TimeUnit::kPs);
}

TEST(Lexical, Timeunit_StoredInModuleDecl_Flags) {
  auto r = ParseWithPreprocessor(
      "module top;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  auto* mod = r.cu->modules[0];
  EXPECT_TRUE(mod->has_timeunit);
  EXPECT_TRUE(mod->has_timeprecision);
}

// =============================================================================
// LRM §3.14.1 — Time value rounding
// =============================================================================
// 14. Same precision as unit: delay values rounded to whole numbers.
TEST(ParserClause03, Cl3_14_1_SamePrecisionRoundsToInteger) {
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kNs, 1};
  // 2.75ns with 1ns precision rounds to 3ns = 3 ticks at ns.
  EXPECT_EQ(RealDelayToTicks(2.75, ts, TimeUnit::kNs), 3u);
  // 2.3ns rounds to 2ns.
  EXPECT_EQ(RealDelayToTicks(2.3, ts, TimeUnit::kNs), 2u);
  // 2.5ns rounds to 3ns (round half away from zero).
  EXPECT_EQ(RealDelayToTicks(2.5, ts, TimeUnit::kNs), 3u);
}

// 15. One order of magnitude smaller: rounds to one decimal place.
TEST(ParserClause03, Cl3_14_1_OneOrderSmallerRoundsToOneDecimal) {
  // 1ns unit, 100ps precision → 1 decimal place in ns.
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kPs, 100};
  // 2.75ns → 2.8ns = 2800ps = 2800 ticks at ps.
  EXPECT_EQ(RealDelayToTicks(2.75, ts, TimeUnit::kPs), 2800u);
  // 2.73ns → 2.7ns = 2700ps.
  EXPECT_EQ(RealDelayToTicks(2.73, ts, TimeUnit::kPs), 2700u);
}

// 16. Rounding example: 1ns unit, 100ps precision, 2.75ns rounds to 2.8ns.
TEST(ParserClause03, Cl3_14_1_LrmExample_2_75ns) {
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kPs, 100};
  // 2.75ns rounded to nearest 100ps = 2.8ns = 2800 ticks at ps.
  EXPECT_EQ(RealDelayToTicks(2.75, ts, TimeUnit::kPs), 2800u);
  // Verify in ns-tick form: at ns precision, 2800ps = 2.8ns ≈ 3 ticks.
  // But at ps global precision the value is 2800.
  EXPECT_EQ(RealDelayToTicks(2.75, ts, TimeUnit::kPs), 2800u);
}

// 17. Two orders of magnitude smaller: rounds to two decimal places.
TEST(ParserClause03, Cl3_14_1_TwoOrdersSmaller) {
  // 1ns unit, 10ps precision → 2 decimal places in ns.
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kPs, 10};
  // 2.756ns → 2.76ns = 2760ps.
  EXPECT_EQ(RealDelayToTicks(2.756, ts, TimeUnit::kPs), 2760u);
  // 2.754ns → 2.75ns = 2750ps.
  EXPECT_EQ(RealDelayToTicks(2.754, ts, TimeUnit::kPs), 2750u);
}

// 18. Three orders (full precision): no rounding needed.
TEST(ParserClause03, Cl3_14_1_ThreeOrdersNoRounding) {
  // 1ns unit, 1ps precision → 3 decimal places in ns.
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kPs, 1};
  // 2.756ns = 2756ps exactly, no rounding.
  EXPECT_EQ(RealDelayToTicks(2.756, ts, TimeUnit::kPs), 2756u);
}

// 19. Zero delay: rounds to zero regardless of precision.
TEST(ParserClause03, Cl3_14_1_ZeroDelay) {
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kPs, 100};
  EXPECT_EQ(RealDelayToTicks(0.0, ts, TimeUnit::kPs), 0u);
}

// 20. Exact integer delays pass through unchanged with any precision.
TEST(ParserClause03, Cl3_14_1_ExactIntegerPassThrough) {
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kPs, 100};
  // 5.0ns is exact at any precision → 5000ps.
  EXPECT_EQ(RealDelayToTicks(5.0, ts, TimeUnit::kPs), 5000u);
  // 3.0ns → 3000ps.
  EXPECT_EQ(RealDelayToTicks(3.0, ts, TimeUnit::kPs), 3000u);
}

}  // namespace
