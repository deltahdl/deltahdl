#include <gtest/gtest.h>

#include <vector>

#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"
#include "simulator/svdpi.h"

using namespace delta;

namespace {

int MyCFunc(int port_id);

void* MyCFuncKey() {
  static int key = 0;
  return &key;
}

class MyCModel {
 public:
  explicit MyCModel(const char* instance_path, int base) : base_(base) {
    svScope scope = svGetScopeFromName(instance_path);
    put_result_ = svPutUserData(scope, MyCFuncKey(), this);
  }

  int PutResult() const { return put_result_; }

  int LocallyMapped(int port_id) const { return base_ + port_id; }

 private:
  int base_;
  int put_result_ = -1;
};

int MyCFunc(int port_id) {
  svScope scope = svGetScope();
  auto* me = static_cast<MyCModel*>(svGetUserData(scope, MyCFuncKey()));
  if (me == nullptr) return -1;
  return me->LocallyMapped(port_id);
}

struct ForeignRuntimeInstalledForExample {
  explicit ForeignRuntimeInstalledForExample(DpiRuntime* rt) {
    DpiSetForeignRuntime(rt);
  }
  ~ForeignRuntimeInstalledForExample() { DpiSetForeignRuntime(nullptr); }
};

struct InstancesRegistered {
  InstancesRegistered() {
    DpiRegisterScope("top.i1_h_09_04");
    DpiRegisterScope("top.i2_h_09_04");
  }
};

struct ExampleOneDesign {
  DpiRuntime rt;
  ForeignRuntimeInstalledForExample installed{&rt};
  InstancesRegistered instances;
  MyCModel model_of_i1{"top.i1_h_09_04", 100};
  MyCModel model_of_i2{"top.i2_h_09_04", 200};

  ExampleOneDesign() {
    DpiRtFunction map_id;
    map_id.sv_name = "MapID";
    map_id.c_name = "MyCFunc";
    map_id.is_context = true;
    map_id.return_type = DataTypeKind::kInt;
    map_id.impl = [](const std::vector<DpiArgValue>& args) -> DpiArgValue {
      return DpiArgValue::FromInt(MyCFunc(args[0].AsInt()));
    };
    rt.RegisterImport(map_id);
  }

  int MapIdCalledFrom(const char* instance_path, int port_id) {
    DpiScope decl_scope;
    decl_scope.name = instance_path;
    rt.EnterContextImportCall("MapID", decl_scope);
    DpiArgValue result =
        rt.CallImport("MapID", {DpiArgValue::FromInt(port_id)});
    rt.LeaveImportCall();
    return result.AsInt();
  }
};

TEST(DpiContextExample, EachModelStoresItselfUnderItsInstanceScope) {
  ExampleOneDesign design;
  EXPECT_EQ(design.model_of_i1.PutResult(), 0);
  EXPECT_EQ(design.model_of_i2.PutResult(), 0);
}

TEST(DpiContextExample, TheImportAnswersFromTheModelOfTheCallingInstance) {
  ExampleOneDesign design;
  EXPECT_EQ(design.MapIdCalledFrom("top.i1_h_09_04", 5), 105);
  EXPECT_EQ(design.MapIdCalledFrom("top.i2_h_09_04", 5), 205);
}

TEST(DpiContextExample, AnInstanceWithoutAModelFindsNoUserData) {
  ExampleOneDesign design;
  DpiRegisterScope("top.i3_h_09_04");
  EXPECT_EQ(design.MapIdCalledFrom("top.i3_h_09_04", 5), -1);
}

}  // namespace
