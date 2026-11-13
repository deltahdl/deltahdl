#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <initializer_list>
#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(LocalVariableElaboration, FormalArgumentRedeclaredInSequenceBodyIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b, c;\n"
      "  sequence sub_seq3(lv);\n"
      "    int lv;\n"
      "    @(posedge clk) (a ##1 lv);\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "is a formal argument and cannot be redeclared", 3,
                            "16.10"));
}

TEST(LocalVariableElaboration, FormalArgumentRedeclaredInPropertyBodyIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  property p(lv);\n"
      "    bit lv;\n"
      "    @(posedge clk) lv |-> b;\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "is a formal argument and cannot be redeclared", 3,
                            "16.10"));
}

TEST(LocalVariableElaboration, LocalFormalArgumentRedeclaredInBodyIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  sequence s(local input int lv);\n"
      "    int lv;\n"
      "    @(posedge clk) (a, b) ##1 b;\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "is a formal argument and cannot be redeclared", 3,
                            "16.10"));
}

TEST(LocalVariableElaboration, FreshBodyLocalAlongsideFormalElaborates) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  sequence s(lv);\n"
      "    int guard;\n"
      "    @(posedge clk) (a, guard = b) ##1 lv;\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(LocalVariableElaboration, InstantiatedSequencesLocalIsNotVisible) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  bit a, b, c, do1;\n"
      "  int data_in, data_out;\n"
      "  sequence sub_seq1;\n"
      "    int v1;\n"
      "    (a ##1 !a, v1 = data_in) ##1 !b[*0:$] ##1 b && (data_out == v1);\n"
      "  endsequence\n"
      "  sequence seq1;\n"
      "    c ##1 sub_seq1 ##1 (do1 == v1);\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'v1' is a local variable of sequence 'sub_seq1' "
                            "and is not visible outside its body",
                            10, "16.10"));
}

TEST(LocalVariableElaboration, LocalOfASequenceNotInstantiatedIsUnresolved) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input logic clk, a);\n"
      "  sequence s1; int v; (a, v = 1) ##1 (v == 1); endsequence\n"
      "  sequence s2(x); x; endsequence\n"
      "  assert property (@(posedge clk) s2(a) ##1 v);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier 'v'", 4,
                            "23.9"));
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), "is a local variable", 4, "16.10"));
}

TEST(LocalVariableFlow, AReferenceToAnUnassignedLocalIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a, b, c;\n"
      "  property p1;\n"
      "    int x;\n"
      "    @(posedge clk) (a, x++) |-> b;\n"
      "  endproperty\n"
      "  property p2;\n"
      "    int y;\n"
      "    @(posedge clk) ((a, y = 1) or b) ##1 (c == y);\n"
      "  endproperty\n"
      "  sequence s3;\n"
      "    int u, v = u + 1;\n"
      "    a;\n"
      "  endsequence\n"
      "  sequence s4;\n"
      "    int w;\n"
      "    (a, w = 1) ##1 (c == w);\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  auto reported = [&](const char* name, int line) {
    return ReportedError(f.diag.Diagnostics(),
                         std::string("the local variable '") + name +
                             "' is referenced at a point where it is "
                             "unassigned",
                         line, "16.10");
  };
  EXPECT_TRUE(reported("x", 5));
  EXPECT_TRUE(reported("y", 9));
  EXPECT_TRUE(reported("u", 12));
  EXPECT_FALSE(reported("w", 17));
}

TEST(LocalVariableFlow, ALocalInsideAnActualOfTriggeredIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a, c;\n"
      "  int data_in;\n"
      "  sequence sub(lv);\n"
      "    (a, lv = data_in) ##1 (lv > 0);\n"
      "  endsequence\n"
      "  sequence top;\n"
      "    int v1;\n"
      "    (c, v1 = 0) ##1 sub(v1 + 1).triggered;\n"
      "  endsequence\n"
      "  sequence top2;\n"
      "    int v1;\n"
      "    (c, v1 = 0) ##1 sub(v1).triggered;\n"
      "  endsequence\n"
      "  sequence top3;\n"
      "    int v1;\n"
      "    (c, v1 = 0) ##1 sub(v1 + 1).matched;\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  const char* const kReport =
      "a local variable passed to an instance that triggered is applied to "
      "shall be an entire actual argument";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 9, "16.10"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 13, "16.10"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a local variable passed to an instance that "
                            "matched is applied to shall be an entire actual "
                            "argument",
                            17, "16.13.5"));
}

TEST(LocalVariableFlow, TriggeredOnASequenceReadingTheFormalFirstIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a, c;\n"
      "  int data_in;\n"
      "  sequence sub(lv);\n"
      "    (a && lv > 0) ##1 (1, lv = data_in);\n"
      "  endsequence\n"
      "  sequence top;\n"
      "    int v1;\n"
      "    (c, v1 = 1) ##1 sub(v1).triggered;\n"
      "  endsequence\n"
      "  sequence top2;\n"
      "    int v1;\n"
      "    (c, v1 = 1) ##1 sub(v1).matched;\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'sub' references its formal 'lv', bound to the "
                            "local variable 'v1', before it assigns it",
                            9, "16.10"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'sub' references its formal 'lv', bound to the "
                            "local variable 'v1', before it assigns it",
                            13, "16.13.5"));
}

TEST(LocalVariableFlow, AnAssignmentOnAnEmptyMatchingSequenceIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a, b, c;\n"
      "  int e;\n"
      "  sequence s;\n"
      "    int x;\n"
      "    @(posedge clk) a ##1 (b[*0:1], x = e) ##1 c[*2];\n"
      "  endsequence\n"
      "  sequence t;\n"
      "    int x;\n"
      "    @(posedge clk) (a ##1 b[*0:1], x = e) ##1 c[*2];\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  const char* const kReport =
      "a local variable assignment may not be attached to a sequence that "
      "admits an empty match";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 6, "16.10"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 10, "16.10"));
}

TEST(LocalVariableFlow,
     AThroughoutConditionReadingAnUnassignedLocalIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a, b;\n"
      "  sequence s;\n"
      "    int x;\n"
      "    @(posedge clk) (x > 0) throughout (a ##1 (b, x = 1));\n"
      "  endsequence\n"
      "  sequence t;\n"
      "    int y;\n"
      "    @(posedge clk) (a, y = 1) ##1 ((y > 0) throughout (a ##1 b));\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the local variable 'x' is referenced at a point "
                            "where it is unassigned",
                            5, "16.10"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "the local variable 'y'", 9,
                             "16.10"));
}

TEST(LocalVariableFlow, AnAssignmentOnAnEmptyMatchInsideAnOrGroupIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a, b, c;\n"
      "  int e;\n"
      "  sequence s;\n"
      "    int x;\n"
      "    @(posedge clk) a ##1 ((b[*0:1], x = e) or c) ##1 c[*2];\n"
      "  endsequence\n"
      "  sequence t;\n"
      "    int x;\n"
      "    @(posedge clk) a ##1 ((a ##1 b[*0:1], x = e) or c) ##1 c[*2];\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  const char* const kReport =
      "a local variable assignment may not be attached to a sequence that "
      "admits an empty match";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 6, "16.10"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 10, "16.10"));
}

TEST(LocalVariableElaboration, ATypedOrUntypedFormalRedeclaredIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a;\n"
      "  sequence s(bit lv, w);\n"
      "    int w;\n"
      "    @(posedge clk) lv;\n"
      "  endsequence\n"
      "  sequence t(untyped lv);\n"
      "    logic lv;\n"
      "    @(posedge clk) a;\n"
      "  endsequence\n"
      "  property p(local input int lv);\n"
      "    int lv;\n"
      "    @(posedge clk) a;\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  const char* const kReport = "is a formal argument and cannot be redeclared";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 3, "16.10"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 7, "16.10"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 11, "16.10"));
}

TEST(LocalVariableElaboration,
     DISABLED_AFormalRedeclaredOutsideAModuleIsError) {
  ElabFixture f;
  ElaborateSrc(
      "interface i;\n"
      "  sequence s(lv); int lv; lv; endsequence\n"
      "endinterface\n"
      "program pr;\n"
      "  sequence s(lv); int lv; lv; endsequence\n"
      "endprogram\n"
      "checker ck;\n"
      "  sequence s(lv); int lv; lv; endsequence\n"
      "endchecker\n"
      "package pk;\n"
      "  sequence s(lv); int lv; lv; endsequence\n"
      "endpackage\n"
      "sequence s_cu(lv); int lv; lv; endsequence\n"
      "module m;\n"
      "  logic clk;\n"
      "  clocking cb @(posedge clk);\n"
      "    sequence s(lv); int lv; lv; endsequence\n"
      "  endclocking\n"
      "  if (1) begin : g\n"
      "    sequence s(lv); int lv; lv; endsequence\n"
      "  end\n"
      "  i u();\n"
      "  ck c();\n"
      "endmodule\n",
      f);
  const char* const kReport = "is a formal argument and cannot be redeclared";
  for (int line : {2, 5, 8, 11, 13, 17, 20}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, line, "16.10"))
        << line;
  }
}

TEST(LocalVariableElaboration,
     DISABLED_ALocalReachingAClockThroughAnActualIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b, c;\n"
      "  sequence t(e); @(posedge e) c; endsequence\n"
      "  sequence s;\n"
      "    logic x;\n"
      "    @(posedge clk) (a, x = b) ##1 t(x);\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "local variable \"x\" may not be used in a clocking event expression", 6,
      "16.10"));
}

TEST(LocalVariableElaboration, ASignalReachingAClockThroughAnActualIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b, c;\n"
      "  sequence t(e); @(posedge e) c; endsequence\n"
      "  sequence s;\n"
      "    logic x;\n"
      "    @(posedge clk) (a, x = b) ##1 t(clk);\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

struct InitializerReadPair {
  const char* bad;
  const char* unassigned;
  const char* good;
};

const InitializerReadPair kInitializerReads[] = {
    {"int u, v = u + 1;", "u", "int u = 1, v = u + 1;"},
    {"int u; int v = u + 1;", "u", "int u = 2; int v = u * 3;"},
    {"int v = w, w = 1;", "w", "int w = 1, v = w;"},
    {"int v = w + 1; int w = 1;", "w", "int w = 1; int v = w + 1;"},
    {"int v = v + 1;", "v", "int t = 1, v = t + 1;"},
};

std::string InitializerSource(const std::string& decl) {
  return "module m;\n"
         "  bit clk, a;\n"
         "  sequence s; " +
         decl +
         " @(posedge clk) a; endsequence\n"
         "  property p; " +
         decl +
         " @(posedge clk) a; endproperty\n"
         "endmodule\n";
}

TEST(LocalInitializerReads,
     AnInitializerReadingAnUninitializedLocalIsReported) {
  for (const InitializerReadPair& pair : kInitializerReads) {
    SCOPED_TRACE(pair.bad);
    ElabFixture f;
    ElaborateSrc(InitializerSource(pair.bad), f);
    const std::string kMessage = std::string("the local variable '") +
                                 pair.unassigned +
                                 "' is referenced at a point where it is"
                                 " unassigned";
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kMessage, 3, "16.10"));
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kMessage, 4, "16.10"));
  }
}

TEST(LocalInitializerReads,
     AnInitializerReadingAnEarlierInitializedLocalIsAccepted) {
  for (const InitializerReadPair& pair : kInitializerReads) {
    SCOPED_TRACE(pair.good);
    ElabFixture f;
    ElaborateSrc(InitializerSource(pair.good), f);
    EXPECT_FALSE(f.diag.HasErrors());
  }
}

constexpr const char* kUnassignedX =
    "the local variable 'x' is referenced at a point where it is unassigned";

std::string WithInitializer(const std::string& text, const char* init) {
  std::string out = text;
  size_t at = out.find("%I");
  if (at != std::string::npos) out.replace(at, 2, init);
  return out;
}

std::string FlowModule(const std::string& decl) {
  return "module m;\n"
         "  logic clk, a, b, c;\n"
         "  logic [3:0] v;\n"
         "  " +
         decl + "\nendmodule\n";
}

void ExpectEachReadReported(std::initializer_list<const char*> decls) {
  for (const char* decl : decls) {
    SCOPED_TRACE(decl);
    ElabFixture f;
    ElaborateSrc(FlowModule(WithInitializer(decl, "")), f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kUnassignedX, 4, "16.10"));
  }
}

void ExpectEachReadAccepted(std::initializer_list<const char*> decls) {
  for (const char* decl : decls) {
    SCOPED_TRACE(decl);
    ElabFixture f;
    ElaborateSrc(FlowModule(WithInitializer(decl, " = 1")), f);
    EXPECT_FALSE(f.diag.HasErrors());
  }
}

#define SEQ(body) "sequence s; int x%I, y; @(posedge clk) " body "; endsequence"
#define PROP(body) \
  "property p; int x%I, y; @(posedge clk) " body "; endproperty"

const std::initializer_list<const char*> kSequenceReads = {
    SEQ("a ##1 (b == x)"),   SEQ("(a, x--)"),          SEQ("(a, ++x)"),
    SEQ("(a, --x)"),         SEQ("(a, x += 1)"),       SEQ("(a, x -= 1)"),
    SEQ("(a, x *= 2)"),      SEQ("(a, x /= 2)"),       SEQ("(a, x %= 2)"),
    SEQ("(a, x &= 1)"),      SEQ("(a, x |= 1)"),       SEQ("(a, x ^= 1)"),
    SEQ("(a, x <<= 1)"),     SEQ("(a, x >>= 1)"),      SEQ("(a, x <<<= 1)"),
    SEQ("(a, x >>>= 1)"),    SEQ("(a, y = x, x = 1)"), SEQ("a ##1 v[x]"),
    SEQ("(a, $display(x))"),
};

const std::initializer_list<const char*> kPropertyReads = {
    PROP("(b == x) |-> a"),         PROP("a |-> (b == x)"),
    PROP("a |-> b ##1 (c == x)"),   PROP("a |-> not (c == x)"),
    PROP("a |-> (c == x) or b"),    PROP("(a, x--) |-> b"),
    PROP("(a, ++x) |-> b"),         PROP("(a, --x) |-> b"),
    PROP("(a, x++) |-> b"),         PROP("(a, x += 1) |-> b"),
    PROP("(a, x -= 1) |-> b"),      PROP("(a, x *= 2) |-> b"),
    PROP("(a, x /= 2) |-> b"),      PROP("(a, x %= 2) |-> b"),
    PROP("(a, x &= 1) |-> b"),      PROP("(a, x |= 1) |-> b"),
    PROP("(a, x ^= 1) |-> b"),      PROP("(a, x <<= 1) |-> b"),
    PROP("(a, x >>= 1) |-> b"),     PROP("(a, x <<<= 1) |-> b"),
    PROP("(a, x >>>= 1) |-> b"),    PROP("a |-> (b ##1 c, x -= 1)"),
    PROP("a |-> strong((b, x++))"), PROP("a |-> (b, x++) ##1 c"),
};

const std::initializer_list<const char*> kGroupOperands = {
    PROP("a |-> (b, x++)"),         PROP("a |=> (b, x += 1)"),
    PROP("a |-> (b, y = x)"),       PROP("(b, x %= 2)"),
    PROP("not (b, x++)"),           PROP("if (a) (b, x++) else c"),
    PROP("if (a) c else (b, x++)"), PROP("a #-# (b, x++)"),
    PROP("a #=# (b, x++)"),         PROP("nexttime (b, x++)"),
    PROP("(b, x++) and c"),         PROP("(b, x++) or c"),
    PROP("a |-> ((b, x++))"),
};

#undef SEQ
#undef PROP

TEST(UnassignedLocalReads, EachSequenceReadIsReported) {
  ExpectEachReadReported(kSequenceReads);
}

TEST(UnassignedLocalReads, EachSequenceReadOfAnInitializedLocalIsAccepted) {
  ExpectEachReadAccepted(kSequenceReads);
}

TEST(UnassignedLocalReads, EachPropertyReadIsReported) {
  ExpectEachReadReported(kPropertyReads);
}

TEST(UnassignedLocalReads, EachPropertyReadOfAnInitializedLocalIsAccepted) {
  ExpectEachReadAccepted(kPropertyReads);
}

TEST(UnassignedLocalReads,
     DISABLED_AGroupStandingAsAPropertyOperandIsReported) {
  ExpectEachReadReported(kGroupOperands);
}

TEST(UnassignedLocalReads,
     AGroupStandingAsAPropertyOperandOfAnInitializedLocalIsAccepted) {
  ExpectEachReadAccepted(kGroupOperands);
}

TEST(UnassignedLocalReads, AReadAfterAnEarlierAssignmentIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      FlowModule("sequence s; int x;\n"
                 "    @(posedge clk) (a, x = 1) ##1 (b, x += 1, ++x, x--)"
                 " ##1 v[x] ##1 (a, $display(x)) ##1 (c == x);\n"
                 "  endsequence\n"
                 "  property p; int x;\n"
                 "    @(posedge clk) (a, x = 1, x *= 2) |-> (b, x <<<= 1)"
                 " ##1 (c == x);\n"
                 "  endproperty"),
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

struct FlowPlace {
  const char* text;
};

const FlowPlace kFlowPlaces[] = {
    {"program pg(input logic clk, a, b);\n"
     "  sequence s; int x%I; @(posedge clk) a ##1 (b == x); endsequence\n"
     "  property p; int x%I; @(posedge clk) a |-> (b == x); endproperty\n"
     "endprogram\n"
     "module m; logic clk, a, b; pg u(clk, a, b); endmodule\n"},
    {"interface ifc(input logic clk, a, b);\n"
     "  sequence s; int x%I; @(posedge clk) a ##1 (b == x); endsequence\n"
     "  property p; int x%I; @(posedge clk) a |-> (b == x); endproperty\n"
     "endinterface\n"
     "module m; logic clk, a, b; ifc u(clk, a, b); endmodule\n"},
    {"checker ck(logic clk, logic a, logic b);\n"
     "  sequence s; int x%I; @(posedge clk) a ##1 (b == x); endsequence\n"
     "  property p; int x%I; @(posedge clk) a |-> (b == x); endproperty\n"
     "endchecker\n"
     "module m; logic clk, a, b; ck u(clk, a, b); endmodule\n"},
};

const FlowPlace kUncheckedFlowPlaces[] = {
    {"package pk;\n"
     "  sequence s(clk, a, b); int x%I; @(posedge clk) a ##1 (b == x);"
     " endsequence\n"
     "  property p(clk, a, b); int x%I; @(posedge clk) a |-> (b == x);"
     " endproperty\n"
     "endpackage\n"
     "module m; endmodule\n"},
    {"package pk;\n"
     "  sequence s(clk, a, b); int x%I; @(posedge clk) a ##1 (b == x);"
     " endsequence\n"
     "  property p(clk, a, b); int x%I; @(posedge clk) a |-> (b == x);"
     " endproperty\n"
     "endpackage\n"
     "module m; import pk::*; logic clk, a, b;\n"
     "  assert property (p(clk, a, b));\n"
     "endmodule\n"},
    {"module m; logic clk, a, b;\n"
     "  if (1) begin : g\n"
     "    sequence s; int x%I; @(posedge clk) a ##1 (b == x); endsequence\n"
     "    property p; int x%I; @(posedge clk) a |-> (b == x); endproperty\n"
     "    assert property (p);\n"
     "  end\n"
     "endmodule\n"},
    {"sequence s(clk, a, b); int x%I; @(posedge clk) a ##1 (b == x);"
     " endsequence\n"
     "property p(clk, a, b); int x%I; @(posedge clk) a |-> (b == x);"
     " endproperty\n"
     "module m; endmodule\n"},
};

std::string PlaceSource(const char* text, const char* init) {
  return WithInitializer(WithInitializer(text, init), init);
}

void ExpectBothDeclarationsReported(const char* text) {
  SCOPED_TRACE(text);
  const std::string kSrc = PlaceSource(text, "");
  ElabFixture f;
  ElaborateSrc(kSrc, f);
  uint32_t sequence_line = LineHolding(kSrc, "sequence s");
  uint32_t property_line = LineHolding(kSrc, "property p");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kUnassignedX, sequence_line,
                            "16.10"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kUnassignedX, property_line,
                            "16.10"));
}

void ExpectBothDeclarationsAccepted(const char* text) {
  SCOPED_TRACE(text);
  ElabFixture f;
  ElaborateSrc(PlaceSource(text, " = 1"), f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(UnassignedLocalReads, AReadInAProgramInterfaceOrCheckerIsReported) {
  for (const FlowPlace& place : kFlowPlaces) {
    ExpectBothDeclarationsReported(place.text);
  }
}

TEST(UnassignedLocalReads, AReadOfAnInitializedLocalInEachPlaceIsAccepted) {
  for (const FlowPlace& place : kFlowPlaces) {
    ExpectBothDeclarationsAccepted(place.text);
  }
  for (const FlowPlace& place : kUncheckedFlowPlaces) {
    ExpectBothDeclarationsAccepted(place.text);
  }
}

TEST(UnassignedLocalReads,
     DISABLED_AReadInAPackageGenerateBlockOrCompilationUnitIsReported) {
  for (const FlowPlace& place : kUncheckedFlowPlaces) {
    ExpectBothDeclarationsReported(place.text);
  }
}

}  // namespace
