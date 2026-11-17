#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(OverriddenSampleMethod, BasicOverrideParses) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      covergroup cg with function sample(bit a, int x);
        coverpoint x;
      endgroup
    endmodule
  )"));
}

TEST(OverriddenSampleMethod, OutputSampleFormalRejected) {
  auto r = Parse(R"(
    module m;
      covergroup cg with function sample(output int x);
        coverpoint x;
      endgroup
    endmodule
  )");
  EXPECT_TRUE(ReportedError(r.diags,
                            "a sample method formal argument cannot designate "
                            "an output direction",
                            3, "19.8.1"));
}

TEST(OverriddenSampleMethod, InoutSampleFormalRejected) {
  auto r = Parse(R"(
    module m;
      covergroup cg with function sample(inout int x);
        coverpoint x;
      endgroup
    endmodule
  )");
  EXPECT_TRUE(ReportedError(r.diags,
                            "a sample method formal argument cannot designate "
                            "an output direction",
                            3, "19.8.1"));
}

TEST(OverriddenSampleMethod, InputSampleFormalAllowed) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      covergroup cg with function sample(input int x);
        coverpoint x;
      endgroup
    endmodule
  )"));
}

TEST(OverriddenSampleMethod, NameSharedBetweenBothListsRejected) {
  auto r = Parse(R"(
    module m;
      covergroup cg (int v) with function sample(int v, bit b);
        coverpoint v;
      endgroup
    endmodule
  )");
  EXPECT_TRUE(ReportedError(r.diags,
                            "sample method formal argument 'v' shares the "
                            "covergroup argument scope and cannot reuse a "
                            "covergroup formal-argument name",
                            3, "19.8.1"));
}

TEST(OverriddenSampleMethod, DistinctNamesAcrossListsAccepted) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      covergroup cg (int w) with function sample(int v, bit b);
        coverpoint v;
      endgroup
    endmodule
  )"));
}

TEST(OverriddenSampleMethod, SharedNameAmongManyFormalsRejected) {
  auto r = Parse(R"(
    module m;
      covergroup cg (int a, ref int data) with function sample(bit c, int data);
        coverpoint c;
      endgroup
    endmodule
  )");
  EXPECT_TRUE(ReportedError(r.diags,
                            "sample method formal argument 'data' shares the "
                            "covergroup argument scope and cannot reuse a "
                            "covergroup formal-argument name",
                            3, "19.8.1"));
}

TEST(OverriddenSampleMethod, DefaultValuedSampleFormalStillCollides) {
  auto r = Parse(R"(
    module m;
      covergroup cg (int v) with function sample(int v = 0);
        coverpoint v;
      endgroup
    endmodule
  )");
  EXPECT_TRUE(ReportedError(r.diags,
                            "sample method formal argument 'v' shares the "
                            "covergroup argument scope and cannot reuse a "
                            "covergroup formal-argument name",
                            3, "19.8.1"));
}

TEST(OverriddenSampleMethod, OutputOnLaterSampleFormalRejected) {
  auto r = Parse(R"(
    module m;
      covergroup cg with function sample(int a, output int b);
        coverpoint a;
      endgroup
    endmodule
  )");
  EXPECT_TRUE(ReportedError(r.diags,
                            "a sample method formal argument cannot designate "
                            "an output direction",
                            3, "19.8.1"));
}

TEST(OverriddenSampleMethod, RefSampleFormalAllowed) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      covergroup cg with function sample(ref int x);
        coverpoint x;
      endgroup
    endmodule
  )"));
}

TEST(OverriddenSampleMethod, SampleFormalInOptionAssignmentRejected) {
  auto r = Parse(R"(
    module m;
      covergroup cg with function sample(bit a, int x);
        coverpoint x;
        option.per_instance = a;
      endgroup
    endmodule
  )");
  EXPECT_TRUE(ReportedError(r.diags,
                            "sample method formal argument 'a' may only "
                            "designate a coverpoint or conditional guard "
                            "expression, not a coverage-option value",
                            5, "19.8.1"));
}

TEST(OverriddenSampleMethod, SampleFormalInTypeOptionAssignmentRejected) {
  auto r = Parse(R"(
    module m;
      covergroup cg with function sample(int weight_src, int x);
        coverpoint x;
        type_option.weight = weight_src;
      endgroup
    endmodule
  )");
  EXPECT_TRUE(ReportedError(r.diags,
                            "sample method formal argument 'weight_src' may "
                            "only designate a coverpoint or conditional guard "
                            "expression, not a coverage-option value",
                            5, "19.8.1"));
}

TEST(OverriddenSampleMethod, SampleFormalInsideOptionValueExpressionRejected) {
  auto r = Parse(R"(
    module m;
      covergroup cg with function sample(int a, int x);
        coverpoint x;
        option.weight = a + 1;
      endgroup
    endmodule
  )");
  EXPECT_TRUE(ReportedError(r.diags,
                            "sample method formal argument 'a' may only "
                            "designate a coverpoint or conditional guard "
                            "expression, not a coverage-option value",
                            5, "19.8.1"));
}

TEST(OverriddenSampleMethod, NonFormalInOptionAssignmentAccepted) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      int w;
      covergroup cg with function sample(bit a, int x);
        coverpoint x;
        option.weight = w;
      endgroup
    endmodule
  )"));
}

TEST(OverriddenSampleMethod, SampleFormalInConditionalGuardAccepted) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      covergroup cg with function sample(bit a, int x);
        coverpoint x iff (a);
      endgroup
    endmodule
  )"));
}

TEST(OverriddenSampleMethod, SampleFormalAsCrossItemAccepted) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      covergroup cg with function sample(bit a, int x);
        coverpoint x;
        cross x, a;
      endgroup
    endmodule
  )"));
}

TEST(OverriddenSampleMethod, SampleFormalInBinRangeRejected) {
  auto r = Parse(R"(
    module m;
      covergroup cg with function sample(int v, int w);
        coverpoint v { bins b = {[0:w]}; }
      endgroup
    endmodule
  )");
  EXPECT_TRUE(ReportedError(r.diags,
                            "sample method formal argument 'w' may only "
                            "designate a coverpoint or conditional guard "
                            "expression, not a bin specification",
                            4, "19.8.1"));
}

TEST(OverriddenSampleMethod, SampleFormalInTransitionRejected) {
  auto r = Parse(R"(
    module m;
      covergroup cg with function sample(int v, int w);
        coverpoint v { bins b = (w => 1); }
      endgroup
    endmodule
  )");
  EXPECT_TRUE(ReportedError(r.diags,
                            "sample method formal argument 'w' may only "
                            "designate a coverpoint or conditional guard "
                            "expression, not a bin specification",
                            4, "19.8.1"));
}

TEST(OverriddenSampleMethod, SampleFormalInBinWithFilterRejected) {
  auto r = Parse(R"(
    module m;
      covergroup cg with function sample(int v, int w);
        coverpoint v { bins b[] = {[0:7]} with (item < w); }
      endgroup
    endmodule
  )");
  EXPECT_TRUE(ReportedError(r.diags,
                            "sample method formal argument 'w' may only "
                            "designate a coverpoint or conditional guard "
                            "expression, not a bin specification",
                            4, "19.8.1"));
}

TEST(OverriddenSampleMethod, SampleFormalInBinArraySizeRejected) {
  auto r = Parse(R"(
    module m;
      covergroup cg with function sample(int v, int w);
        coverpoint v { bins b[w] = {[0:7]}; }
      endgroup
    endmodule
  )");
  EXPECT_TRUE(ReportedError(r.diags,
                            "sample method formal argument 'w' may only "
                            "designate a coverpoint or conditional guard "
                            "expression, not a bin specification",
                            4, "19.8.1"));
}

TEST(OverriddenSampleMethod, SampleFormalInIllegalBinsValueRejected) {
  auto r = Parse(R"(
    module m;
      covergroup cg with function sample(int v, int w);
        coverpoint v { illegal_bins b = {w}; }
      endgroup
    endmodule
  )");
  EXPECT_TRUE(ReportedError(r.diags,
                            "sample method formal argument 'w' may only "
                            "designate a coverpoint or conditional guard "
                            "expression, not a bin specification",
                            4, "19.8.1"));
}

TEST(OverriddenSampleMethod, SampleFormalInCoverpointOptionRejected) {
  auto r = Parse(R"(
    module m;
      covergroup cg with function sample(int v, int w);
        coverpoint v { option.weight = w; }
      endgroup
    endmodule
  )");
  EXPECT_TRUE(ReportedError(r.diags,
                            "sample method formal argument 'w' may only "
                            "designate a coverpoint or conditional guard "
                            "expression, not a coverage-option value",
                            4, "19.8.1"));
}

TEST(OverriddenSampleMethod, SampleFormalInCrossOptionRejected) {
  auto r = Parse(R"(
    module m;
      covergroup cg with function sample(int v, int w);
        a: coverpoint v;
        b: coverpoint w;
        X: cross a, b { option.weight = w; }
      endgroup
    endmodule
  )");
  EXPECT_TRUE(ReportedError(r.diags,
                            "sample method formal argument 'w' may only "
                            "designate a coverpoint or conditional guard "
                            "expression, not a coverage-option value",
                            6, "19.8.1"));
}

TEST(OverriddenSampleMethod, SampleFormalInCrossIntersectRejected) {
  auto r = Parse(R"(
    module m;
      covergroup cg with function sample(int v, int w);
        a: coverpoint v;
        b: coverpoint w;
        X: cross a, b { bins s = binsof(a) intersect {w}; }
      endgroup
    endmodule
  )");
  EXPECT_TRUE(ReportedError(r.diags,
                            "sample method formal argument 'w' may only "
                            "designate a coverpoint or conditional guard "
                            "expression, not a cross bin select expression",
                            6, "19.8.1"));
}

TEST(OverriddenSampleMethod, SampleFormalInCrossWithRejected) {
  auto r = Parse(R"(
    module m;
      covergroup cg with function sample(int v, int w, int lim);
        a: coverpoint v;
        b: coverpoint w;
        X: cross a, b { bins s = X with (a < lim); }
      endgroup
    endmodule
  )");
  EXPECT_TRUE(ReportedError(r.diags,
                            "sample method formal argument 'lim' may only "
                            "designate a coverpoint or conditional guard "
                            "expression, not a cross bin select expression",
                            6, "19.8.1"));
}

TEST(OverriddenSampleMethod, SampleFormalInBinGuardAccepted) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      covergroup cg with function sample(int v, bit en);
        coverpoint v { bins b = {[0:3]} iff (en); }
      endgroup
    endmodule
  )"));
}

TEST(OverriddenSampleMethod, SampleFormalInCrossBinGuardAccepted) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      covergroup cg with function sample(int v, int w, bit en);
        a: coverpoint v;
        b: coverpoint w;
        X: cross a, b { bins s = binsof(a) iff (en); }
      endgroup
    endmodule
  )"));
}

std::string InScope(const char* scope, const char* header, const char* body) {
  return std::string(scope) + " s;\n  covergroup cg" + header + ";\n" + body +
         "  endgroup\nend" + scope + "\n";
}

const char* const kOutputDirection =
    "a sample method formal argument cannot designate an output direction";

std::string SharedName(const char* name) {
  return std::string("sample method formal argument '") + name +
         "' shares the covergroup argument scope and cannot reuse a "
         "covergroup formal-argument name";
}

std::string OnlyCoverpointOrGuard(const char* context) {
  return std::string(
             "sample method formal argument 'w' may only designate a "
             "coverpoint or conditional guard expression, not a ") +
         context;
}

struct ForbiddenUse {
  const char* body;
  uint32_t line;
  const char* context;
};

const ForbiddenUse kForbiddenUses[] = {
    {"    coverpoint v;\n    option.weight = w;\n", 4, "coverage-option value"},
    {"    coverpoint v;\n    type_option.weight = w;\n", 4,
     "coverage-option value"},
    {"    coverpoint v;\n    option.weight = w + 1;\n", 4,
     "coverage-option value"},
    {"    coverpoint v { bins b = {[0:w]}; }\n", 3, "bin specification"},
    {"    coverpoint v { bins b = (w => 1); }\n", 3, "bin specification"},
    {"    coverpoint v { bins b[] = {[0:7]} with (item < w); }\n", 3,
     "bin specification"},
    {"    coverpoint v { bins b[w] = {[0:7]}; }\n", 3, "bin specification"},
    {"    coverpoint v { illegal_bins b = {w}; }\n", 3, "bin specification"},
    {"    coverpoint v { option.weight = w; }\n", 3, "coverage-option value"},
    {"    a: coverpoint v;\n    b: coverpoint u;\n"
     "    X: cross a, b { option.weight = w; }\n",
     5, "coverage-option value"},
    {"    a: coverpoint v;\n    b: coverpoint u;\n"
     "    X: cross a, b { bins s = binsof(a) intersect {w}; }\n",
     5, "cross bin select expression"},
    {"    a: coverpoint v;\n    b: coverpoint u;\n"
     "    X: cross a, b { bins s = X with (a < w); }\n",
     5, "cross bin select expression"},
};

const char* const kAllowedUses[] = {
    "    coverpoint w;\n",
    "    coverpoint v iff (w);\n",
    "    coverpoint v { bins b = {[0:3]} iff (w); }\n",
    ("    a: coverpoint v;\n    b: coverpoint u;\n"
     "    X: cross a, b { bins s = binsof(a) iff (w); }\n"),
    "    coverpoint v;\n    cross v, w;\n",
};

void ExpectEachForbiddenUseRejected(const char* scope) {
  for (const auto& use : kForbiddenUses) {
    SCOPED_TRACE(use.body);
    auto r = Parse(
        InScope(scope, " with function sample(int v, int u, int w)", use.body));
    EXPECT_TRUE(ReportedError(r.diags, OnlyCoverpointOrGuard(use.context),
                              use.line, "19.8.1"));
  }
}

void ExpectEachAllowedUseAccepted(const char* scope) {
  for (const char* body : kAllowedUses) {
    SCOPED_TRACE(body);
    EXPECT_TRUE(ParseOk(
        InScope(scope, " with function sample(int v, int u, int w)", body)));
  }
}

TEST(OverriddenSampleMethod, ClassCovergroupFormalOutsideCoverpointRejected) {
  ExpectEachForbiddenUseRejected("class");
}

TEST(OverriddenSampleMethod, ClassCovergroupFormalAsCoverpointAccepted) {
  ExpectEachAllowedUseAccepted("class");
}

TEST(OverriddenSampleMethod, PackageCovergroupFormalOutsideCoverpointRejected) {
  ExpectEachForbiddenUseRejected("package");
}

TEST(OverriddenSampleMethod, PackageCovergroupFormalAsCoverpointAccepted) {
  ExpectEachAllowedUseAccepted("package");
}

void ExpectOutputDirectionsRejected(const char* scope) {
  for (const char* header : {" with function sample(output int x)",
                             " with function sample(inout int x)",
                             " with function sample(int a, output int x)"}) {
    SCOPED_TRACE(header);
    auto r = Parse(InScope(scope, header, "    coverpoint x;\n"));
    EXPECT_TRUE(ReportedError(r.diags, kOutputDirection, 2, "19.8.1"));
  }
}

void ExpectInputAndRefAccepted(const char* scope) {
  for (const char* header : {" with function sample(input int x)",
                             " with function sample(ref int x)"}) {
    SCOPED_TRACE(header);
    EXPECT_TRUE(ParseOk(InScope(scope, header, "    coverpoint x;\n")));
  }
}

TEST(OverriddenSampleMethod, ClassCovergroupOutputSampleFormalRejected) {
  ExpectOutputDirectionsRejected("class");
}

TEST(OverriddenSampleMethod, ClassCovergroupInputOrRefSampleFormalAllowed) {
  ExpectInputAndRefAccepted("class");
}

TEST(OverriddenSampleMethod, PackageCovergroupOutputSampleFormalRejected) {
  ExpectOutputDirectionsRejected("package");
}

TEST(OverriddenSampleMethod, PackageCovergroupInputOrRefSampleFormalAllowed) {
  ExpectInputAndRefAccepted("package");
}

void ExpectSharedNameRejected(const char* scope) {
  auto r = Parse(InScope(scope, " (int v) with function sample(int v, bit b)",
                         "    coverpoint v;\n"));
  EXPECT_TRUE(ReportedError(r.diags, SharedName("v"), 2, "19.8.1"));
  EXPECT_TRUE(
      ParseOk(InScope(scope, " (int w) with function sample(int v, bit b)",
                      "    coverpoint v;\n")));
}

TEST(OverriddenSampleMethod, ClassCovergroupNameSharedBetweenListsRejected) {
  ExpectSharedNameRejected("class");
}

TEST(OverriddenSampleMethod, PackageCovergroupNameSharedBetweenListsRejected) {
  ExpectSharedNameRejected("package");
}

}  // namespace
