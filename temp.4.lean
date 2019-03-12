import vec

def time : peirce.space := peirce.space.mk 0
def geom : peirce.space := peirce.space.mk 1
def v1 : peirce.vec geom := ( peirce.vec.mkVector geom 0.000000 0.000000 0.000000 )
def v2 : peirce.vec geom := ( peirce.vec.mkVector geom 0.000000 0.000000 0.000000 )
def v3 : peirce.vec geom := ( peirce.add ( ( peirce.add ( v2 : peirce.vec geom ) ( v1 : peirce.vec geom ) : peirce.space geom ) ) : peirce.space geom ) ( peirce.add ( v1 : peirce.vec geom ) ( v2 : peirce.vec geom ) : peirce.space geom ) : peirce.space geom )

