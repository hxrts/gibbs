import Mathlib

/-! # Session Types

Vocabulary for multiparty session typing: session identifiers, roles, labels,
endpoints, and directed communication edges. These types are used by the
choreography bridges in the Hamiltonian and ContinuumField layers.
-/

namespace Gibbs

/-! ## Session Types -/

abbrev SessionId := Nat
abbrev Role := String
abbrev Label := String

/-- An endpoint identifies a participant's view within a session. -/
structure Endpoint where
  sid : SessionId
  role : Role
deriving DecidableEq, Repr

/-- A directed edge represents a communication channel from sender to receiver. -/
structure Edge where
  sid : SessionId
  sender : Role
  receiver : Role
deriving DecidableEq, Repr

/-- Construct the sender endpoint of an edge. -/
def Edge.senderEp (e : Edge) : Endpoint :=
  { sid := e.sid, role := e.sender }

/-- Construct the receiver endpoint of an edge. -/
def Edge.receiverEp (e : Edge) : Endpoint :=
  { sid := e.sid, role := e.receiver }

/-- Construct an edge from an endpoint to a target role. -/
def Endpoint.edgeTo (ep : Endpoint) (target : Role) : Edge :=
  { sid := ep.sid, sender := ep.role, receiver := target }

end Gibbs
