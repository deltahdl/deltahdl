// Tests for IEEE 1800-2023 §7.9.11 -- associative array literals.
//
// §7.9.11 defines four runtime rules, all observed here end-to-end (parse ->
// elaborate -> lower -> run) so the behavior reflects the production read/
// write/method paths rather than a hand-built AssocArrayObject:
//   * an array's contents may be written one entry at a time or replaced whole
//     by an '{index:value} literal, at declaration or in a procedural assign;
//   * with a default defined, a read of a missing index returns that default
//     and issues no warning;
//   * with no default, a missing read returns the element type's Table 7-1
//     default (§7.4.5): 0 for a 2-state element, all-x for a 4-state element;
//   * a defined default does not change the associative array methods.
//
// The value expressions in a literal are constant expressions in a declaration
// initializer, so the literal / parameter / localparam value forms are each
// exercised (they take different constant-evaluation paths).

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// --- Claim: a literal establishes the array contents (declaration form) ------

// A string-keyed literal with a trailing default seeds the named entries; a
// read of a present key returns its value.
TEST(AssocLiteral, DeclLiteralStringKeysSeedsEntries) {
  auto v = RunAndGet(
      "module t;\n"
      "  integer tab[string] = '{\"Peter\":20, \"Paul\":22, \"Mary\":23, "
      "default:-1};\n"
      "  int result;\n"
      "  initial result = tab[\"Peter\"];\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 20u);
}

// An integer-keyed literal seeds a present entry read back at runtime.
TEST(AssocLiteral, DeclLiteralIntKeysSeedsEntries) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int] = '{3:30, 7:70};\n"
      "  int result;\n"
      "  initial result = aa[7];\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 70u);
}

// A literal value that is a parameter reference (constant-expression form
// distinct from an integer literal) is evaluated into the seeded entry.
TEST(AssocLiteral, DeclLiteralValueFromParameter) {
  auto v = RunAndGet(
      "module t;\n"
      "  parameter integer P = 22;\n"
      "  integer tab[string] = '{\"x\":P, default:-1};\n"
      "  int result;\n"
      "  initial result = tab[\"x\"];\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 22u);
}

// A literal value that is a localparam reference: a second constant-expression
// form exercising the same seeding path.
TEST(AssocLiteral, DeclLiteralValueFromLocalparam) {
  auto v = RunAndGet(
      "module t;\n"
      "  localparam int Q = 33;\n"
      "  int aa[int] = '{5:Q};\n"
      "  int result;\n"
      "  initial result = aa[5];\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 33u);
}

// --- Claim: whole-array replacement by a literal in a procedural assign
// -------

// A runtime literal assignment replaces the contents wholesale: the count
// reflects only the new entries.
TEST(AssocLiteral, RuntimeLiteralReplacesWholeContents) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[1] = 10;\n"
      "    aa[2] = 20;\n"
      "    aa = '{5:50, 6:60};\n"
      "    result = aa.num();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 2u);
}

// Prior entries are discarded by the replacement: a formerly present key now
// reads back the 2-state Table 7-1 default (0).
TEST(AssocLiteral, RuntimeLiteralDropsPriorEntries) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[1] = 10;\n"
      "    aa = '{5:50, 6:60};\n"
      "    result = aa[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

// The replacement establishes its new entries.
TEST(AssocLiteral, RuntimeLiteralEstablishesNewEntry) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[1] = 10;\n"
      "    aa = '{5:50, 6:60};\n"
      "    result = aa[6];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 60u);
}

// String-keyed whole replacement via a runtime literal.
TEST(AssocLiteral, RuntimeLiteralStringKeyedReplaces) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[string];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[\"old\"] = 1;\n"
      "    aa = '{\"x\":5, \"y\":9};\n"
      "    result = aa[\"y\"] + aa.num();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 11u);
}

// A default supplied by a runtime replacement literal governs later missing
// reads.
TEST(AssocLiteral, RuntimeLiteralDefaultGovernsMissingRead) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa = '{5:50, default:77};\n"
      "    result = aa[999];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 77u);
}

// --- Claim: default defined -> missing read returns default, no warning
// -------

// A default-only literal makes every missing read return the default value.
TEST(AssocLiteral, DeclDefaultOnlyReturnsDefaultOnMissingRead) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int] = '{default:99};\n"
      "  int result;\n"
      "  initial result = aa[7];\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 99u);
}

// Integer-keyed: a missing read with a default returns the default AND leaves
// the warning count unchanged. Driven inline so the diagnostic engine is
// observable; the default arrives from real declaration syntax.
TEST(AssocLiteral, DefaultReadIntKeyIssuesNoWarning) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int aa[int] = '{1:10, default:77};\n"
      "  int result;\n"
      "  initial result = aa[999];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  f.ctx.RunFinalBlocks();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

// String-keyed variant of the no-warning rule.
TEST(AssocLiteral, DefaultReadStringKeyIssuesNoWarning) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int aa[string] = '{\"a\":10, default:55};\n"
      "  int result;\n"
      "  initial result = aa[\"missing\"];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  f.ctx.RunFinalBlocks();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 55u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

// --- Claim: no default -> missing read returns Table 7-1 default (§7.4.5)
// -----

// 2-state integer element, no default: a missing read yields 0.
TEST(AssocLiteral, MissingReadNoDefaultIntKeyReturnsZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int] = '{1:10};\n"
      "  int result;\n"
      "  initial result = aa[999];\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

// 2-state string-keyed element, no default: a missing read yields 0.
TEST(AssocLiteral, MissingReadNoDefaultStringKeyReturnsZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[string] = '{\"a\":1};\n"
      "  int result;\n"
      "  initial result = aa[\"b\"];\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

// 4-state element (integer), no default: a missing read yields the all-x
// Table 7-1 default (§7.4.5). $isunknown reports 1 when any bit is x/z, so the
// unknown default is observable end-to-end.
TEST(AssocLiteral, MissingReadNoDefault4StateReturnsX) {
  auto v = RunAndGet(
      "module t;\n"
      "  integer aa[int] = '{1:10};\n"
      "  int result;\n"
      "  initial result = $isunknown(aa[999]);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

// --- Claim: a defined default does not affect the array methods --------------

// num() counts only the real entries, ignoring the default.
TEST(AssocLiteral, DefaultDoesNotAffectNum) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int] = '{1:10, 2:20, default:99};\n"
      "  int result;\n"
      "  initial result = aa.num();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 2u);
}

// size() (equivalent count method) likewise ignores the default.
TEST(AssocLiteral, DefaultDoesNotAffectSize) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int] = '{5:50, default:0};\n"
      "  int result;\n"
      "  initial result = aa.size();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

// exists() on a missing key returns 0 even though a default is defined: the
// default must not make a nonexistent key appear present.
TEST(AssocLiteral, DefaultDoesNotAffectExistsMissing) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int] = '{1:10, default:99};\n"
      "  int result;\n"
      "  initial result = aa.exists(999);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

// first() selects the smallest real index, not the default.
TEST(AssocLiteral, DefaultDoesNotAffectFirst) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int] = '{10:1, 20:2, default:99};\n"
      "  int k;\n"
      "  int d;\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = aa.first(k);\n"
      "    result = k;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 10u);
}

// last() selects the largest real index, not the default.
TEST(AssocLiteral, DefaultDoesNotAffectLast) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int] = '{10:1, 20:2, default:99};\n"
      "  int k;\n"
      "  int d;\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = aa.last(k);\n"
      "    result = k;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 20u);
}

// next() traverses only the real entries; the default is not a traversal stop.
TEST(AssocLiteral, DefaultDoesNotAffectNext) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int] = '{10:1, 20:2, default:99};\n"
      "  int k;\n"
      "  int d;\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = aa.first(k);\n"
      "    d = aa.next(k);\n"
      "    result = k;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 20u);
}

// prev() traverses only the real entries in reverse.
TEST(AssocLiteral, DefaultDoesNotAffectPrev) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int] = '{10:1, 20:2, default:99};\n"
      "  int k;\n"
      "  int d;\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = aa.last(k);\n"
      "    d = aa.prev(k);\n"
      "    result = k;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 10u);
}

// delete() removes a real entry regardless of a defined default.
TEST(AssocLiteral, DefaultDoesNotAffectDelete) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int] = '{10:1, 20:2, default:99};\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa.delete(10);\n"
      "    result = aa.num();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

}  // namespace
