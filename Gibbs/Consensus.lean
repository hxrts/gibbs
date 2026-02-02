import Gibbs.Consensus.Basic
import Gibbs.Consensus.Observation
import Gibbs.Consensus.Decision
import Gibbs.Consensus.Adversary
import Gibbs.Consensus.TranscriptDistance
import Gibbs.Consensus.InteractiveDistance
import Gibbs.Consensus.PartitionFunction
import Gibbs.Consensus.OrderParameter
import Gibbs.Consensus.Gap
import Gibbs.Consensus.Quorum
import Gibbs.Consensus.Thresholds
import Gibbs.Consensus.UniversalityClasses
import Gibbs.Consensus.CodingBridge
import Gibbs.Consensus.CodingDistance
import Gibbs.Consensus.Certificates
import Gibbs.Consensus.Hamiltonian
import Gibbs.Consensus.SafetyLiveness
import Gibbs.Consensus.ChannelThreshold
import Gibbs.Consensus.Examples.RepetitionCode
import Gibbs.Consensus.Examples.QuorumBFT
import Gibbs.Consensus.Examples.NakamotoSketch

/-!
# Consensus layer facade

Single entry point for the consensus-as-statistical-mechanics framework.
Importing this file brings in the full stack: execution model, observation
and decision maps, adversary model, transcript and interactive distances,
partition functions, energy gaps, quorum systems, Byzantine thresholds,
universality classes, the coding-theory bridge, and worked examples
(repetition code, quorum BFT, Nakamoto sketch), plus channel-capacity
thresholds.
-/
