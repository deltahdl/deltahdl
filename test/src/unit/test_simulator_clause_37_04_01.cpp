#include <gtest/gtest.h>

#include <string>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.4.1 (Diagram key for objects and classes) is the legend for the data
// model diagrams. It introduces no BNF and states one shall: an unnamed class
// groups objects only for convenience and shall not be referenced as a group
// elsewhere. Its remaining content is the notational distinction the diagrams
// draw - an object *definition* (where an object's properties live) versus an
// object *reference* (a depiction of an object defined elsewhere), and a
// *class* (a named grouping of differing object kinds) versus a plain object.
//
// Those distinctions are not decoration; the existing simulator object model
// already embodies them, and the public VPI routines apply them. A definition
// answers its own property queries; a reference reaches the object it stands
// for; a named class constant gathers a group of differing kinds, while an
// unnamed convenience grouping has no name to be reached by. These tests drive
// a private VpiContext through the public C entry points - exactly as a PLI
// program would - and observe each notation being honored.
class VpiObjectsAndClasses : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext ctx_;
};

// Object definition (bold letters, solid enclosure): the properties of the
// object are defined at this location. A definition therefore answers its own
// property queries directly - vpi_get() and vpi_get_str() read the values
// stored on the defining object itself.
TEST_F(VpiObjectsAndClasses, ObjectDefinitionLocationHoldsItsProperties) {
  VpiObject defn;
  defn.type = vpiNet;
  defn.name = "w1";
  defn.size = 8;

  // The properties live where the object is defined, so they come straight off
  // the definition handle.
  EXPECT_EQ(vpi_get(vpiSize, &defn), 8);
  const char* name = vpi_get_str(vpiName, &defn);
  ASSERT_NE(name, nullptr);
  EXPECT_EQ(std::string(name), "w1");
}

// Object reference (normal letters, solid enclosure): a reference is a separate
// depiction of an object that is defined elsewhere. It is a distinct handle
// from the definition, and it does not carry the definition's properties - it
// reaches them. The model's reference link (reported through vpiActual) bridges
// the reference back to the defining object, where the properties are read.
TEST_F(VpiObjectsAndClasses, ObjectReferenceReachesTheObjectDefinedElsewhere) {
  VpiObject defn;
  defn.type = vpiNet;
  defn.name = "w1";
  defn.size = 8;

  VpiObject ref;
  ref.type = vpiRefObj;  // a reference, not the definition
  ref.actual = &defn;

  // The reference is its own handle, not the definition.
  EXPECT_NE(&ref, &defn);

  // Following the reference lands on the object defined elsewhere...
  vpiHandle reached = VpiHandleC(vpiActual, &ref);
  ASSERT_EQ(reached, &defn);
  // ...and the properties are those of the definition, read at the definition.
  EXPECT_EQ(vpi_get(vpiSize, reached), 8);
}

// Class definition (bold italic letters, dotted enclosure): a class groups
// other objects (and classes). Referencing the class by name gathers the
// members of the group, even when they are of differing object kinds - which a
// single object type never does. Here the named assertion class collects both
// an assert and a cover under one reference, while the plain object type
// vpiAssert matches only the assert.
TEST_F(VpiObjectsAndClasses, NamedClassGroupsObjectsOfDifferingKinds) {
  VpiObject scope;
  scope.type = vpiModule;

  VpiObject a;
  a.type = vpiAssert;
  VpiObject c;
  c.type = vpiCover;
  scope.children.push_back(&a);
  scope.children.push_back(&c);

  // The class name references the whole group - two differing kinds together.
  vpiHandle iter = vpi_iterate(vpiAssertion, &scope);
  ASSERT_NE(iter, nullptr);
  EXPECT_EQ(vpi_scan(iter), &a);
  EXPECT_EQ(vpi_scan(iter), &c);
  EXPECT_EQ(vpi_scan(iter), nullptr);

  // A plain object type is not a class: it matches its one kind only.
  vpiHandle assert_iter = vpi_iterate(vpiAssert, &scope);
  ASSERT_NE(assert_iter, nullptr);
  EXPECT_EQ(vpi_scan(assert_iter), &a);
  EXPECT_EQ(vpi_scan(assert_iter), nullptr);
}

// Class definition, continued: a class definition can contain an object
// definition - the grouped member is not a bare reference but a full object
// whose own properties are defined at that location. Reaching a member through
// the class and then querying it observes that: the contained object answers
// its own type and name straight off itself, the way any object definition
// does.
TEST_F(VpiObjectsAndClasses, ClassDefinitionContainsAnObjectDefinition) {
  VpiObject scope;
  scope.type = vpiModule;

  VpiObject contained;
  contained.type = vpiAssert;  // an object definition held within the class
  contained.name = "a1";
  scope.children.push_back(&contained);

  // Reach the contained object by referencing the class...
  vpiHandle iter = vpi_iterate(vpiAssertion, &scope);
  ASSERT_NE(iter, nullptr);
  vpiHandle member = vpi_scan(iter);
  ASSERT_EQ(member, &contained);
  EXPECT_EQ(vpi_scan(iter), nullptr);

  // ...and it is a definition: its properties are defined on the member itself.
  EXPECT_EQ(vpi_get(vpiType, member), vpiAssert);
  const char* name = vpi_get_str(vpiName, member);
  ASSERT_NE(name, nullptr);
  EXPECT_EQ(std::string(name), "a1");
}

// Unnamed class (dotted enclosure, no name): objects may be grouped for
// convenience, but such a grouping shall not be referenced as a group
// elsewhere - so no name is given to it. The only groupings the implementation
// lets you reference are the named classes and the plain object types; an
// arbitrary convenience pairing has no single name that spans it. A net placed
// beside the assertions belongs to no class that also holds them: the named
// assertion class excludes it, and its own type vpiNet excludes the assertions.
// No one reference returns the net-plus-assertion grouping as a group.
TEST_F(VpiObjectsAndClasses, UnnamedConvenienceGroupingIsNotReferenceable) {
  VpiObject scope;
  scope.type = vpiModule;

  VpiObject a;
  a.type = vpiAssert;
  VpiObject n;
  n.type = vpiNet;
  n.name = "w1";
  scope.children.push_back(&a);
  scope.children.push_back(&n);

  // The named class references the assertion but never extends to span the net.
  vpiHandle class_iter = vpi_iterate(vpiAssertion, &scope);
  ASSERT_NE(class_iter, nullptr);
  EXPECT_EQ(vpi_scan(class_iter), &a);
  EXPECT_EQ(vpi_scan(class_iter), nullptr);  // the net is not in the group

  // The net is reachable only by its own object-type name, which in turn never
  // pulls in the assertion. The {net, assertion} grouping has no group name.
  vpiHandle net_iter = vpi_iterate(vpiNet, &scope);
  ASSERT_NE(net_iter, nullptr);
  EXPECT_EQ(vpi_scan(net_iter), &n);
  EXPECT_EQ(vpi_scan(net_iter), nullptr);  // the assertion is not in the group
}

}  // namespace
}  // namespace delta
