#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/eval.h"

using namespace delta;

namespace {

TEST(ClassSim, StaticPropertySharedAcrossInstances) {
  SimFixture f;
  auto* type = MakeClassType(f, "Shared", {"inst_val"});
  type->properties.push_back({"counter", 32, true});
  type->static_properties["counter"] = MakeLogic4VecVal(f.arena, 32, 0);

  MakeObj(f, type);
  MakeObj(f, type);

  type->static_properties["counter"] = MakeLogic4VecVal(f.arena, 32, 42);

  EXPECT_EQ(type->static_properties["counter"].ToUint64(), 42u);
}

}  // namespace
