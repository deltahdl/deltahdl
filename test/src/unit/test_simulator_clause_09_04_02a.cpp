// §9.4.2: Event control

#include <gtest/gtest.h>

#include <cstdint>

enum class Logic4 : uint8_t {
  kVal0 = 0,
  kVal1 = 1,
  kX = 2,
  kZ = 3,
};

enum class EdgeKind : uint8_t {
  kNone,
  kPosedge,
  kNegedge,
};

EdgeKind DetectEdge(Logic4 from, Logic4 to) {
  if (from == to)
    return EdgeKind::kNone;
  if (from == Logic4::kVal0 &&
      (to == Logic4::kVal1 || to == Logic4::kX || to == Logic4::kZ))
    return EdgeKind::kPosedge;
  if ((from == Logic4::kX || from == Logic4::kZ) && to == Logic4::kVal1)
    return EdgeKind::kPosedge;
  if (from == Logic4::kVal1 &&
      (to == Logic4::kVal0 || to == Logic4::kX || to == Logic4::kZ))
    return EdgeKind::kNegedge;
  if ((from == Logic4::kX || from == Logic4::kZ) && to == Logic4::kVal0)
    return EdgeKind::kNegedge;
  return EdgeKind::kNone;
}

bool IsEdge(Logic4 from, Logic4 to) {
  EdgeKind e = DetectEdge(from, to);
  return e == EdgeKind::kPosedge || e == EdgeKind::kNegedge;
}

namespace {

TEST(TimingControl, Posedge0To1) {
  EXPECT_EQ(DetectEdge(Logic4::kVal0, Logic4::kVal1), EdgeKind::kPosedge);
}

TEST(TimingControl, Posedge0ToX) {
  EXPECT_EQ(DetectEdge(Logic4::kVal0, Logic4::kX), EdgeKind::kPosedge);
}

TEST(TimingControl, Posedge0ToZ) {
  EXPECT_EQ(DetectEdge(Logic4::kVal0, Logic4::kZ), EdgeKind::kPosedge);
}

TEST(TimingControl, PosedgeXTo1) {
  EXPECT_EQ(DetectEdge(Logic4::kX, Logic4::kVal1), EdgeKind::kPosedge);
}

TEST(TimingControl, PosedgeZTo1) {
  EXPECT_EQ(DetectEdge(Logic4::kZ, Logic4::kVal1), EdgeKind::kPosedge);
}

TEST(TimingControl, Negedge1To0) {
  EXPECT_EQ(DetectEdge(Logic4::kVal1, Logic4::kVal0), EdgeKind::kNegedge);
}

TEST(TimingControl, Negedge1ToX) {
  EXPECT_EQ(DetectEdge(Logic4::kVal1, Logic4::kX), EdgeKind::kNegedge);
}

TEST(TimingControl, Negedge1ToZ) {
  EXPECT_EQ(DetectEdge(Logic4::kVal1, Logic4::kZ), EdgeKind::kNegedge);
}

TEST(TimingControl, NegedgeXTo0) {
  EXPECT_EQ(DetectEdge(Logic4::kX, Logic4::kVal0), EdgeKind::kNegedge);
}

TEST(TimingControl, NegedgeZTo0) {
  EXPECT_EQ(DetectEdge(Logic4::kZ, Logic4::kVal0), EdgeKind::kNegedge);
}

TEST(TimingControl, NoEdge0To0) {
  EXPECT_EQ(DetectEdge(Logic4::kVal0, Logic4::kVal0), EdgeKind::kNone);
}

TEST(TimingControl, NoEdge1To1) {
  EXPECT_EQ(DetectEdge(Logic4::kVal1, Logic4::kVal1), EdgeKind::kNone);
}

TEST(TimingControl, NoEdgeXToX) {
  EXPECT_EQ(DetectEdge(Logic4::kX, Logic4::kX), EdgeKind::kNone);
}

TEST(TimingControl, NoEdgeXToZ) {
  EXPECT_EQ(DetectEdge(Logic4::kX, Logic4::kZ), EdgeKind::kNone);
}

TEST(TimingControl, NoEdgeZToX) {
  EXPECT_EQ(DetectEdge(Logic4::kZ, Logic4::kX), EdgeKind::kNone);
}

TEST(TimingControl, NoEdgeZToZ) {
  EXPECT_EQ(DetectEdge(Logic4::kZ, Logic4::kZ), EdgeKind::kNone);
}

TEST(TimingControl, EdgeDetectedOnPosedge) {
  EXPECT_TRUE(IsEdge(Logic4::kVal0, Logic4::kVal1));
}

TEST(TimingControl, EdgeDetectedOnNegedge) {
  EXPECT_TRUE(IsEdge(Logic4::kVal1, Logic4::kVal0));
}

TEST(TimingControl, NoEdgeDetectedOnSame) {
  EXPECT_FALSE(IsEdge(Logic4::kVal0, Logic4::kVal0));
}

TEST(TimingControl, NoEdgeDetectedXToZ) {
  EXPECT_FALSE(IsEdge(Logic4::kX, Logic4::kZ));
}

} // namespace
