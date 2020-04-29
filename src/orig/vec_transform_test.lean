import PhysL

def time : peirce.space := peirce.space.mk 0
def geom : peirce.space := peirce.space.mk 1
def r2o2 : peirce.scalar  := ( 0 : peirce.scalar )
def v1 : peirce.vec time := ( peirce.vec.mkVector 0 0 0 )
def v2 : peirce.vec _ := ( v1 : peirce.vec _ )
def r11 : peirce.vec geom := ( peirce.vec.mkVector 0 0 0 )
def r12 : peirce.vec _ := ( peirce.vec.mkVector 0 0 0 )
def r13 : peirce.vec geom := ( peirce.vec.mkVector 0 0 0 )
def r14 : peirce.vector_expression _ := ( peirce.vector_expression.vector_literal r11 )
def r15 : peirce.vector_expression geom := ( peirce.vector_expression.vector_literal r12 ) -- Lean doesn't realize r12 : vec geom
def res1 : peirce.vec _ := ( peirce.transform_apply ( rotation1 : peirce.transform _ _ )  ( v1 : peirce.vec _ ) : peirce.vec geom )
def r21 : peirce.vec _ := ( peirce.vec.mkVector 0 0 0 )
def r22 : peirce.vec _ := ( peirce.vec.mkVector 0 0 0 )
def r23 : peirce.vec _ := ( peirce.vec.mkVector 0 0 0 )
def s11 : peirce.vec time := ( peirce.vec.mkVector 0 0 0 )
def s12 : peirce.vec _ := ( peirce.vec.mkVector 0 0 0 )
def s13 : peirce.vec _ := ( peirce.vec.mkVector 0 0 0 )
def sh1 : peirce.vec _ := ( peirce.vec.mkVector 0 0 0 )
def sh2 : peirce.vec _ := ( peirce.vec.mkVector 0 0 0 )
def sh3 : peirce.vec _ := ( peirce.vec.mkVector 0 0 0 )
def p1 : peirce.vec _ := ( peirce.vec.mkVector 0 0 0 )
def p2 : peirce.vec _ := ( peirce.vec.mkVector 0 0 0 )
def p3 : peirce.vec _ := ( peirce.vec.mkVector 0 0 0 )
def c1 : peirce.vec _ := ( peirce.vec.mkVector 0 0 0 )
def c2 : peirce.vec _ := ( peirce.vec.mkVector 0 0 0 )
def c3 : peirce.vec _ := ( peirce.vec.mkVector 0 0 0 )
def res2 : peirce.vec _ := ( peirce.transform_apply ( scale1 : peirce.transform _ _ )  ( v2 : peirce.vec _ ) : peirce.vec _ )
def res3 : peirce.vec _ := ( peirce.transform_apply ( projection : peirce.transform _ _ )  ( v1 : peirce.vec _ ) : peirce.vec _ )
def res4 : peirce.vec _ := ( peirce.transform_apply ( rotate_and_scale : peirce.transform _ _ )  ( v1 : peirce.vec time ) : peirce.vec _ )
def rotation1 : peirce.transform _ _ := ( peirce.transform.mkTransform _ _ ( r11 : peirce.vec _ ) ( r12 : peirce.vec _ ) ( r13 : peirce.vec _ ) )
def rotation2 : peirce.transform geom geom := ( peirce.transform.mkTransform _ _ ( r21 : peirce.vec _ ) ( r22 : peirce.vec _ ) ( r23 : peirce.vec _ ) )
def scale1 : peirce.transform _ _ := ( peirce.transform.mkTransform _ _ ( s11 : peirce.vec _ ) ( s12 : peirce.vec _ ) ( s13 : peirce.vec _ ) )
def sheer1 : peirce.transform _ _ := ( peirce.transform.mkTransform _ _ ( sh1 : peirce.vec _ ) ( sh2 : peirce.vec _ ) ( sh3 : peirce.vec _ ) )
def projection : peirce.transform _ _ := ( peirce.transform.mkTransform time geom ( p1 : peirce.vec _ ) ( p2 : peirce.vec _ ) ( p3 : peirce.vec _ ) )
def double_rotate : peirce.transform _ _ := ( peirce.tcompose ( rotation1 : peirce.transform _ _ )  ( rotation2 : peirce.transform _ _ )  : peirce.transform time geom
def rotate_and_scale : peirce.transform _ _ := ( peirce.tcompose ( double_rotate : peirce.transform _ _ )  ( scale1 : peirce.transform _ _ )  : peirce.transform _ _
def cob1 : peirce.transform _ _ := ( peirce.transform.mkTransform _ _ ( c1 : peirce.vec _ ) ( c2 : peirce.vec _ ) ( c3 : peirce.vec _ ) )
#check ( res4 : peirce.vec _ ) == ( peirce.transform_apply ( rotation2 : peirce.transform _ _ )  ( peirce.transform_apply ( rotation1 : peirce.transform _ _ )  ( v1 : peirce.vec _ ) : peirce.vec _ ) : peirce.vec _ )
#check ( res4 : peirce.vec _ ) == ( peirce.transform_apply ( scale1 : peirce.transform _ _ )  ( res4 : peirce.vec _ ) : peirce.vec _ )
#check ( res3 : peirce.vec _ ) == ( peirce.transform_apply ( peirce.tcompose ( scale1 : peirce.transform _ _ )  ( peirce.tcompose ( rotation2 : peirce.transform _ _ )  ( rotation1 : peirce.transform _ _ )  : peirce.transform _ _ : peirce.transform _ _ ( v1 : peirce.vec _ ) : peirce.vec _ )
#check ( res2 : peirce.vec _ ) == ( peirce.transform_apply ( scale1 : peirce.transform _ _ )  ( v2 : peirce.vec _ ) : peirce.vec _ )
#check ( res2 : peirce.vec _ ) == ( peirce.transform_apply ( peirce.tcompose ( scale1 : peirce.transform _ _ )  ( projection : peirce.transform _ _ )  : peirce.transform _ _ ( v2 : peirce.vec _ ) : peirce.vec _ )
#check ( res2 : peirce.vec _ ) == ( peirce.transform_apply ( scale1 : peirce.transform _ _ )  ( ( ( peirce.transform_apply ( scale1 : peirce.transform time time )  ( v1 : peirce.vec _ ) : peirce.vec _ ) ) : peirce.vec _ ) : peirce.vec _ )
#check ( rotate_and_scale : peirce.transform _ _ )  == ( peirce.tcompose ( double_rotate : peirce.transform _ _ )  ( scale1 : peirce.transform _ _ )  : peirce.transform _ _
#check ( rotate_and_scale : peirce.transform _ _ )  == ( peirce.tcompose ( double_rotate : peirce.transform _ _ )  ( scale1 : peirce.transform _ _ )  : peirce.transform _ _
#check ( rotate_and_scale : peirce.transform _ _ )  == ( cob1 : peirce.transform geom time ) 
