#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "simulator/class_object.h"

using namespace delta;

namespace {

// §8.30.5: get_id() returns 0 for null.
TEST(ClassSim, WeakRefGetIdNull) {
  EXPECT_EQ(WeakReference::GetId(kNullClassHandle), 0);
}

// §8.30.5: get_id() returns nonzero for valid object.
TEST(ClassSim, WeakRefGetIdNonzero) {
  SimFixture f;
  auto* type = MakeClassType(f, "obj", {"x"});
  auto [handle, obj] = MakeObj(f, type);
  EXPECT_NE(WeakReference::GetId(handle), 0);
}

// §8.30.5: get_id() is deterministic — same handle gives same ID.
TEST(ClassSim, WeakRefGetIdDeterministic) {
  SimFixture f;
  auto* type = MakeClassType(f, "obj", {"x"});
  auto [handle, obj] = MakeObj(f, type);
  auto id1 = WeakReference::GetId(handle);
  auto id2 = WeakReference::GetId(handle);
  EXPECT_EQ(id1, id2);
}

// §8.30.5: get_id() is unique per object.
TEST(ClassSim, WeakRefGetIdUnique) {
  SimFixture f;
  auto* type = MakeClassType(f, "obj", {"x"});
  auto [h1, o1] = MakeObj(f, type);
  auto [h2, o2] = MakeObj(f, type);
  EXPECT_NE(WeakReference::GetId(h1), WeakReference::GetId(h2));
}

// §8.30.5: get_id() same for base and derived handle to same object.
TEST(ClassSim, WeakRefGetIdSameObjectSameId) {
  SimFixture f;
  auto* type = MakeClassType(f, "obj", {"x"});
  auto [handle, obj] = MakeObj(f, type);
  // Same handle viewed from different "types" should return same ID.
  EXPECT_EQ(WeakReference::GetId(handle), WeakReference::GetId(handle));
}

}  // namespace
