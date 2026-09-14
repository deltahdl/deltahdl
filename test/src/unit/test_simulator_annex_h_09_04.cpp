#include <gtest/gtest.h>

#include <vector>

#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"
#include "simulator/svdpi.h"

using namespace delta;

namespace {

// §H.9.4, the C side of Example 1: a C++ model class whose instances have a
// one-to-one correspondence with instances of the SystemVerilog module that
// imports MyCFunc. Each model is constructed with the instance path of its
// SystemVerilog scope, resolves that path to an svScope and stores itself
// under that scope with the address of MyCFunc as the user key; MyCFunc,
// called from SystemVerilog, retrieves the scope of its own context with
// svGetScope, looks itself up under the same key and answers from the model
// that belongs to the calling instance.

int MyCFunc(int port_id);

// The user key of the example is the address of MyCFunc, an address of a
// static C symbol as §H.9.3 suggests. A function's address is not a void*
// in ISO C++, so the key here is the address of a static object beside the
// function, which is as unique among all keys as the function's own.
void* MyCFuncKey() {
  static int key = 0;
  return &key;
}

class MyCModel {
 public:
  explicit MyCModel(const char* instance_path, int base) : base_(base) {
    // The clause's svGetScopeByName is the svGetScopeFromName of §H.9.3, the
    // one function in svdpi.h that retrieves a scope by its fully qualified
    // name (the example predates the name the interface settled on).
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
  // Retrieve the SystemVerilog instance scope, this function's context, and
  // the model stored under it.
  svScope scope = svGetScope();
  auto* me = static_cast<MyCModel*>(svGetUserData(scope, MyCFuncKey()));
  if (me == nullptr) return -1;
  return me->LocallyMapped(port_id);
}

// Installs `rt` as the registry the C layer reaches for the length of a case
// and takes it back out afterwards, the installation being process-wide.
struct ForeignRuntimeInstalledForExample {
  explicit ForeignRuntimeInstalledForExample(DpiRuntime* rt) {
    DpiSetForeignRuntime(rt);
  }
  ~ForeignRuntimeInstalledForExample() { DpiSetForeignRuntime(nullptr); }
};

// The design of the example: a module m importing MapID as MyCFunc,
// instantiated twice as top.i1 and top.i2, each instance having its own C
// model. Elaboration is what registers an instance scope by name in a run;
// here DpiRegisterScope stands in for it before the models are constructed.
struct InstancesRegistered {
  InstancesRegistered() {
    DpiRegisterScope("top.i1_h_09_04");
    DpiRegisterScope("top.i2_h_09_04");
  }
};

struct ExampleOneDesign {
  DpiRuntime rt;
  ForeignRuntimeInstalledForExample installed{&rt};
  // Declared ahead of the models so that their scopes exist when each model
  // resolves its instance path.
  InstancesRegistered instances;
  MyCModel model_of_i1{"top.i1_h_09_04", 100};
  MyCModel model_of_i2{"top.i2_h_09_04", 200};

  ExampleOneDesign() {
    DpiRtFunction map_id;
    map_id.sv_name = "MapID";
    map_id.c_name = "MyCFunc";
    map_id.is_context = true;
    map_id.return_type = DataTypeKind::kInteger;
    map_id.impl = [](const std::vector<DpiArgValue>& args) -> DpiArgValue {
      return DpiArgValue::FromInt(MyCFunc(args[0].AsInt()));
    };
    rt.RegisterImport(map_id);
  }

  // SystemVerilog code in the instance `instance_path` calling MapID(port_id):
  // the call opens a context chain in the instantiated scope surrounding the
  // import's declaration and runs the import in it.
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

// Each model's constructor stored itself under its instance's scope, which
// svPutUserData reports with 0.
TEST(DpiContextExample, EachModelStoresItselfUnderItsInstanceScope) {
  ExampleOneDesign design;
  EXPECT_EQ(design.model_of_i1.PutResult(), 0);
  EXPECT_EQ(design.model_of_i2.PutResult(), 0);
}

// MapID called from top.i1 reaches top.i1's model, whose mapping of port 5 is
// 105, and called from top.i2 reaches top.i2's, whose mapping is 205: the
// scope svGetScope reports inside the import is the one the instance path
// resolved to when the model stored itself.
TEST(DpiContextExample, TheImportAnswersFromTheModelOfTheCallingInstance) {
  ExampleOneDesign design;
  EXPECT_EQ(design.MapIdCalledFrom("top.i1_h_09_04", 5), 105);
  EXPECT_EQ(design.MapIdCalledFrom("top.i2_h_09_04", 5), 205);
}

// Called from an instance no model was constructed for, the import finds no
// user data under its scope: what it retrieves is the model of its own
// context and not a model stored under any other.
TEST(DpiContextExample, AnInstanceWithoutAModelFindsNoUserData) {
  ExampleOneDesign design;
  DpiRegisterScope("top.i3_h_09_04");
  EXPECT_EQ(design.MapIdCalledFrom("top.i3_h_09_04", 5), -1);
}

}  // namespace
