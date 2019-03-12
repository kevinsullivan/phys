import vec

def time : peirce.space := peirce.space.mk 0
def geom : peirce.space := peirce.space.mk 1
def v1 : vec geom := ( peirce.vec.mkVector geom 0.000000 0.000000 0.000000 )
def v2 : vec geom := ( peirce.vec.mkVector geom 0.000000 0.000000 0.000000 )
def v3 : vec geom := ( add ( ( add ( v2 : vector geom ) ( v1 : vector geom ) : g
eom ) ) : geom ) ( add ( v1 : vector geom ) ( v2 : vector geom ) : geom ) : geom
 )
