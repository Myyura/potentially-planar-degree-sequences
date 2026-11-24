import SparseBoundary.GraphContractionCheck
import SparseBoundary.GraphContractionLayer6

namespace SparseBoundary.Graph.ContractionLayer7

/-- Triangulated supergraphs used by the contraction certificates. -/
def graphs : Array (Graph 7) :=
  #[⟨0x1dba6f⟩, ⟨0x1db6eb⟩, ⟨0x1f36cf⟩, ⟨0x15e77b⟩, ⟨0x17dd6b⟩]

private def row0 : Array (Nat × Nat) :=
  #[(0,0x5432100), (0,0x2514030), (0,0x2130445), (0,0x4210350), (0,0), (0,0x2130045), (1,0x5403210), (0,0), (0,0), (1,0x1422350), (0,0), (0,0x4512350), (0,0x2514530), (0,0x4212350), (0,0), (0,0x514230), (0,0x132405), (0,0), (0,0x2312054), (1,0x1412350), (0,0x2214530)]
private def row1 : Array (Nat × Nat) :=
  #[(0,0x5432100), (0,0x2345010), (0,0), (0,0x4520310), (0,0), (0,0x2345510), (0,0x5402130), (0,0x4512310), (0,0), (0,0x4522310), (0,0x5024130), (0,0), (0,0x2154130), (0,0x5424130), (0,0), (0,0x452130), (0,0x4512340), (0,0), (0,0x2342510), (0,0x5452130), (0,0x2254130)]
private def row2 : Array (Nat × Nat) :=
  #[(0,0x2435100), (0,0x2345010), (1,0x4253110), (0,0x2130450), (0,0), (0,0), (0,0x2401530), (1,0x4253150), (0,0), (1,0x4233150), (0,0x2053140), (0,0), (1,0x4253210), (1,0x4353210), (0,0), (0,0), (0,0x2435120), (0,0x2345210), (0,0x2132450), (0,0x2523410), (0,0x2253140)]
private def row3 : Array (Nat × Nat) :=
  #[(0,0x3542100), (0,0x4532010), (0,0), (0,0x5420130), (0,0x1452320), (0,0x4532210), (0,0x5302140), (0,0), (0,0x5412130), (0,0x5322140), (0,0x5042130), (0,0), (0,0), (0,0x5242130), (0,0x5442130), (0,0x542130), (0,0x3542130), (0,0), (0,0x2542130), (0,0), (0,0x5542130)]
private def row4 : Array (Nat × Nat) :=
  #[(0,0x4531200), (0,0x2413050), (0,0), (0,0x5210430), (0,0), (0,0x5214430), (0,0x2501430), (0,0), (0,0x2541430), (0,0), (0,0x5012430), (0,0x4531250), (0,0x4231250), (0,0), (0,0x2551430), (0,0x521430), (0,0x5413250), (0,0x2413250), (0,0x5215430), (0,0), (0,0x2251430)]

private def certs := #[row0, row1, row2, row3, row4]

set_option maxRecDepth 131072
set_option maxHeartbeats 0

theorem known : ∀ G∈graphs,G.Planar := planar_layer (certs:=certs) (by decide)
  ContractionLayer6.known (by decide +kernel)

end SparseBoundary.Graph.ContractionLayer7
