# go-AlgebraicProgram-SNARK
**UNDER CONSTRUCTION**

zkSNARK toolchain for learning purpose. 
Attempt to extend the language from quadratic arithmetic programs to
an algebraic circuit based zkSNARK.
Eg. we use circuits with (+ , - , * , / , g^ ) where g is a generator point of the EC Group G1. 
Theoretic description is in the unfinished ![PDF](algebraicProgramSNARK.pdf).

Note that this scheme is not secure since blind evaluation is restricted to the gates indices rather then to an arbitrary 
point in the underlying finite field, however
somebody may come up with a smart idea how to overcome this issue.
It would be nice, since a shielded transaction (Zcash) would take milliseconds instead of seconds!
