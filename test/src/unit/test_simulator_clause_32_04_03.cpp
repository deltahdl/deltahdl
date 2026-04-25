#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "simulator/sdf_parser.h"
#include "simulator/specify.h"

using namespace delta;

namespace {

// =============================================================================
// §32.4.3 — SDF annotation of specparams
// =============================================================================

// §32.4.3 sentence 1: "The SDF LABEL construct annotates to specparams."
// The page-927 example wraps two specparam values inside an ABSOLUTE
// directive — each `(identifier delval)` entry must reach the manager's
// specparam store so the matching SystemVerilog declaration receives the
// new value.
TEST(SdfLabelAnnotation, LabelFlowsThroughAnnotatorToSpecparamValues) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "clk_gen")
        (INSTANCE u1)
        (LABEL
          (ABSOLUTE
            (dhigh 60)
            (dlow 40)))))
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));

  SpecifyManager mgr;
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  const auto& vals = mgr.GetSpecparamValues();
  ASSERT_EQ(vals.size(), 2u);
  EXPECT_EQ(vals[0].name, "dhigh");
  EXPECT_EQ(vals[0].value, 60u);
  EXPECT_EQ(vals[1].name, "dlow");
  EXPECT_EQ(vals[1].value, 40u);
}

// §32.4.3 sentence 1: now that LABEL is decoded into specparams it is no
// longer surfaced through §32.3's "unable to annotate" warning channel.
// The LRM's ownership rule for §32.4 sentence 4 ("LABEL section contains
// new values for specparams") is only satisfied when LABEL data lands as
// a typed specparam annotation rather than a string-named warning.
TEST(SdfLabelAnnotation, LabelDoesNotProduceUnannotatableWarning) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "c")
        (INSTANCE u)
        (LABEL
          (ABSOLUTE
            (cap 12)))))
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));

  SpecifyManager mgr;
  SdfAnnotationResult result =
      AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  for (const auto& w : result.warnings) {
    EXPECT_EQ(w.find("LABEL"), std::string::npos)
        << "LABEL must not warn now that §32.4.3 owns it: " << w;
  }
}

// §32.4.3 sentence 1, degenerate input: an empty ABSOLUTE body carries no
// specparam updates. The parser must accept the construct and the
// annotator must produce zero manager entries — the rule's "annotates"
// reduces to a no-op when no entries are present, rather than raising a
// parse error or fabricating a placeholder specparam.
TEST(SdfLabelAnnotation, EmptyLabelBodyProducesNoSpecparams) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "c")
        (INSTANCE u)
        (LABEL (ABSOLUTE))))
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));

  SpecifyManager mgr;
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  EXPECT_TRUE(mgr.GetSpecparamValues().empty());
}

// §32.4.3 sentence 1, accumulation: a single CELL may carry more than
// one LABEL section, and every entry across all of them must reach the
// manager. The rule applies per-construct, so two LABEL blocks targeting
// disjoint specparam names both land their values without one section
// shadowing the other.
TEST(SdfLabelAnnotation, MultipleLabelSectionsAllContribute) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "c")
        (INSTANCE u)
        (LABEL (ABSOLUTE (a 1)))
        (LABEL (ABSOLUTE (b 2)))))
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));

  SpecifyManager mgr;
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  const auto& vals = mgr.GetSpecparamValues();
  ASSERT_EQ(vals.size(), 2u);
  EXPECT_EQ(vals[0].name, "a");
  EXPECT_EQ(vals[0].value, 1u);
  EXPECT_EQ(vals[1].name, "b");
  EXPECT_EQ(vals[1].value, 2u);
}

// §32.4.3 sentence 2: "Any expression containing one or more specparams
// is reevaluated when annotated to from an SDF file." The manager must
// expose a hook that consumers (specify path delays, procedural delays)
// register against to be notified when an SDF specparam annotation
// updates the value they depend on.
TEST(SdfSpecparamReevaluation, RegisteredCallbackFiresOnSdfAnnotation) {
  SpecifyManager mgr;

  uint64_t observed = 0;
  int call_count = 0;
  mgr.RegisterSpecparamReevaluation("cap", [&](uint64_t v) {
    observed = v;
    ++call_count;
  });

  SdfFile file;
  SdfCell cell;
  SdfSpecparam sp;
  sp.name = "cap";
  sp.value.typ_val = 5;
  cell.specparams.push_back(sp);
  file.cells.push_back(cell);
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  EXPECT_EQ(call_count, 1);
  EXPECT_EQ(observed, 5u);
}

// §32.4.3 sentence 2: only the expressions that reference the annotated
// specparam are reevaluated. A callback registered against a different
// specparam name must not fire when an unrelated specparam is updated,
// because that callback does not represent an "expression containing"
// the SDF-touched specparam.
TEST(SdfSpecparamReevaluation, UnrelatedNameDoesNotFireCallback) {
  SpecifyManager mgr;

  int touched = 0;
  mgr.RegisterSpecparamReevaluation("dhigh", [&](uint64_t) { ++touched; });

  SdfFile file;
  SdfCell cell;
  SdfSpecparam sp;
  sp.name = "dlow";
  sp.value.typ_val = 7;
  cell.specparams.push_back(sp);
  file.cells.push_back(cell);
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  EXPECT_EQ(touched, 0);
}

// §32.4.3 sentence 2: the rule says "any" expression — multiple
// independently registered consumers of the same specparam must each
// observe the new value. The page-928 example illustrates this: a
// specparam can be referenced both inside a procedural delay (#cap) and
// inside a path-delay expression (1.4 * cap + 0.7), and a single LABEL
// update must fan out to both.
TEST(SdfSpecparamReevaluation, MultipleCallbacksAllFire) {
  SpecifyManager mgr;

  int a = 0;
  int b = 0;
  uint64_t va = 0;
  uint64_t vb = 0;
  mgr.RegisterSpecparamReevaluation("cap", [&](uint64_t v) { ++a; va = v; });
  mgr.RegisterSpecparamReevaluation("cap", [&](uint64_t v) { ++b; vb = v; });

  SdfFile file;
  SdfCell cell;
  SdfSpecparam sp;
  sp.name = "cap";
  sp.value.typ_val = 9;
  cell.specparams.push_back(sp);
  file.cells.push_back(cell);
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  EXPECT_EQ(a, 1);
  EXPECT_EQ(b, 1);
  EXPECT_EQ(va, 9u);
  EXPECT_EQ(vb, 9u);
}

// §32.4.3 sentence 2: a path-delay expression of the form
// `(A => Z) = 1.4 * cap + 0.7` must be recomputed when SDF annotates
// `cap`. Modeling the LRM example, register a reevaluator that recomputes
// the expression and writes the result onto a target value, then drive
// two successive LABEL annotations with different `cap` values. The
// dependent value must track each new specparam.
TEST(SdfSpecparamReevaluation, ExpressionContainingSpecparamRecomputesEachTime) {
  SpecifyManager mgr;

  // Stand-in for the LRM example's "1.4 * cap + 0.7" path delay
  // expression. Stored as integers so the test does not depend on
  // floating-point representation.
  uint64_t path_delay = 0;
  mgr.RegisterSpecparamReevaluation("cap", [&](uint64_t cap) {
    path_delay = 14 * cap + 7;
  });

  auto annotate = [&](uint64_t cap_value) {
    SdfFile file;
    SdfCell cell;
    SdfSpecparam sp;
    sp.name = "cap";
    sp.value.typ_val = cap_value;
    cell.specparams.push_back(sp);
    file.cells.push_back(cell);
    AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);
  };

  annotate(0);
  EXPECT_EQ(path_delay, 7u);

  annotate(5);
  EXPECT_EQ(path_delay, 77u);

  annotate(10);
  EXPECT_EQ(path_delay, 147u);
}

}  // namespace
