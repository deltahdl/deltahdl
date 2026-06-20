#ifndef DELTA_ELABORATOR_INTERFACE_SYNTAX_H
#define DELTA_ELABORATOR_INTERFACE_SYNTAX_H

#include <cstdint>
#include <vector>

namespace delta {

// Models the two scoping rules the prose of IEEE 1800-2023 §25.3 imposes on
// interface instances that participate in hierarchical references. The
// surrounding grammar (interface_declaration, modport_declaration,
// interface_instantiation, ...) is borrowed from Annex A and owned there; what
// §25.3 contributes on top of it are the constraints encoded below.

// §25.3: each step a hierarchical reference takes on its way to the interface
// (or interface modport) named as an interface-port-connection actual.
enum class InterfaceHierRefStep : std::uint8_t {
  kInterfaceInstance,       // descends into / names an interface instance
  kArrayedInstanceElement,  // an element selected out of an instance array
  kGenerateBlock,           // a generate-block scope
  kNonInterface,            // names something that is not an interface instance
};

// §25.3: when the actual of an interface port connection is a hierarchical
// reference to an interface, or to a modport of a hierarchically referenced
// interface, the reference must terminate at an interface instance and must not
// pass through an arrayed instance or a generate block along the way. A
// trailing modport name does not change the requirement: the path of instance
// steps must still resolve to an interface instance. An empty path names
// nothing and is therefore not a legal interface-port actual.
bool InterfacePortHierRefIsLegal(const std::vector<InterfaceHierRefStep>& path);

// §25.3: where the parameter targeted by a defparam sits relative to the
// instance that encloses the defparam.
enum class DefparamReach : std::uint8_t {
  kWithinInstance,   // the target lies inside the instance's own hierarchy
  kOutsideInstance,  // the target lies above or beside the instance
};

// §25.3: a defparam located within an instance whose port actuals refer to an
// arrayed interface may only override a parameter that lies within that
// instance's own hierarchy; reaching outside such an instance is illegal. When
// the instance's port actuals do not refer to an arrayed interface, §25.3 adds
// no constraint and the override is permitted from the standpoint of this rule.
bool ArrayedInterfaceDefparamIsLegal(bool instance_has_arrayed_interface_actual,
                                     DefparamReach reach);

}  // namespace delta

#endif  // DELTA_ELABORATOR_INTERFACE_SYNTAX_H
