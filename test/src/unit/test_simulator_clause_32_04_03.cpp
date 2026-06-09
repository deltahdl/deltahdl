#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "simulator/sdf_parser.h"
#include "simulator/specify.h"

using namespace delta;

namespace {

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

TEST(SdfSpecparamReevaluation, ExpressionContainingSpecparamRecomputesEachTime) {
  SpecifyManager mgr;

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

}
