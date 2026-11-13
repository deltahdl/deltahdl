#include <gtest/gtest.h>

#include <string>

#include "elaborator/sequence_degeneracy.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(SequenceProperty, SequenceUsedAsPropertyMustNotAdmitEmptyMatch) {
  EXPECT_FALSE(IsSequenceUsageLegal(SequenceUsageContext::kAsProperty,
                                    SequenceMatchClass::kAdmitsOnlyEmpty));
  EXPECT_FALSE(IsSequenceUsageLegal(SequenceUsageContext::kAsProperty,
                                    SequenceMatchClass::kAdmitsNoMatch));
  EXPECT_TRUE(
      IsSequenceUsageLegal(SequenceUsageContext::kAsProperty,
                           SequenceMatchClass::kAdmitsAtLeastOneNonempty));
}

constexpr const char* kEmptyMatchReport =
    "it shall be nondegenerate and admit no empty match";

std::string EmptyMatchModule(const std::string& items) {
  return "module m;\n"
         "  logic clk; bit a, b;\n"
         "  sequence s_empty; a[*0:2]; endsequence\n"
         "  sequence s_never; a intersect (a ##1 a); endsequence\n"
         "  sequence s_full; a[*1:2]; endsequence\n" +
         items + "endmodule\n";
}

constexpr int kItemLine = 6;

const char* const kEmptyMatchingForms[] = {
    "strong(a[*0])",
    "weak(a[*0])",
    "strong(a[*0:1])",
    "weak(a[*0:1])",
    "strong(a[*0:$])",
    "weak(b[*0] ##0 a)",
    "strong(a intersect (a ##1 a))",
    "weak(a intersect (a ##1 a))",
};

const char* const kEmptyMatchingInstances[] = {
    "strong(s_empty)", "weak(s_empty)", "strong(s_never)", "weak(s_never)"};

const char* const kNonemptyForms[] = {
    "strong(a[*1])",   "weak(a[*1:2])",       "strong(a[*0] ##1 b)",
    "weak(a ##1 b)",   "strong(s_full)",      "weak(s_full)",
    "strong(a[*1:$])", "weak(a[*0:1] ##1 b)",
};

std::string InDirective(const char* directive, const char* form) {
  std::string item = "  ";
  item += directive;
  item += " property (@(posedge clk) ";
  item += form;
  item += ");\n";
  return EmptyMatchModule(item);
}

std::string InDeclaration(const char* form) {
  std::string item = "  property p; ";
  item += form;
  item += "; endproperty\n  assert property (@(posedge clk) p);\n";
  return EmptyMatchModule(item);
}

void ExpectEmptyMatchReported(const char* form) {
  for (const char* directive : {"assert", "assume", "cover"}) {
    SCOPED_TRACE(std::string(directive) + " " + form);
    ElabFixture f;
    ElaborateSrc(InDirective(directive, form), f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kEmptyMatchReport,
                              kItemLine, "16.12.22"));
  }
  SCOPED_TRACE(std::string("declaration ") + form);
  ElabFixture f;
  ElaborateSrc(InDeclaration(form), f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kEmptyMatchReport, kItemLine,
                            "16.12.22"));
}

TEST(SequenceProperty, AStrengthOverAnEmptyOrNoMatchIsReported) {
  for (const char* form : kEmptyMatchingForms) ExpectEmptyMatchReported(form);
}

TEST(SequenceProperty,
     DISABLED_AStrengthOverAnEmptyOrNoMatchInstanceIsReported) {
  for (const char* form : kEmptyMatchingInstances) {
    ExpectEmptyMatchReported(form);
  }
}

TEST(SequenceProperty, AStrengthOverANonemptyMatchIsAccepted) {
  for (const char* form : kNonemptyForms) {
    for (const char* directive : {"assert", "assume", "cover"}) {
      SCOPED_TRACE(std::string(directive) + " " + form);
      ElabFixture f;
      ElaborateSrc(InDirective(directive, form), f);
      EXPECT_FALSE(f.diag.HasErrors());
    }
    SCOPED_TRACE(std::string("declaration ") + form);
    ElabFixture f;
    ElaborateSrc(InDeclaration(form), f);
    EXPECT_FALSE(f.diag.HasErrors());
  }
}

}  // namespace
