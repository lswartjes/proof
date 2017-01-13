X   := { "x_0", "x_m_1", "x_m_2" }:
X_0 := { "x_0" }:
X_m := { "x_m_1", "x_m_2" }:
X_f := { "x_m_1", "x_m_2" }:

T := table(
    "x_0" = { [ "x_m_1", FALSE ], [ "x_m_2", FALSE ] },
    "x_m_1" = { },
    "x_m_2" = { }
   ):

_unsafe_reach := proc( x )
    local y;
begin
    { op( y, 1 ) $ y in select( T[ x ], ( y ) -> bool( op( y, 2 ) ) ) }
end_proc:

_reach := proc( x )
    local y;
begin
    { op( y, 1 ) $ y in T[ x ] }
end_proc:

_back_reach := proc( x )
    local y, _T;
begin
    _T := select( T, ( y ) -> has( op( y, 2 ), x ) ):
    { op( y, 1 ) $ y in _T }
end_proc:

_forward_paths := proc( x, X )
    local idx, p, P, Q;
begin
    idx := 1:
    P := table( 1 = { [ x ] } ):
    repeat
        P[ idx + 1 ] := { }:
        for p in P[ idx ] do
            for y in _reach( p[ -1 ] ) do
                if bool( contains( p, y ) = 0 ) then
                    P[ idx + 1 ] := P[ idx + 1 ] union { p.[ y ] }:
                end_if:
            end_for:
        end_for:
        idx := idx + 1:
    until bool( nops( P[ idx ] ) = 0 ) end_repeat:
    Q := { }:
    for idx from 1 to idx do
        Q := Q union { p $ p in select( P[ idx ], ( p ) -> bool( p[ -1 ] in X ) ) }:
    end_for:
end_proc:

_backward_paths := proc( x, X )
    local idx, P, Q;
begin
    idx := 1:
    P := table( 1 = { [ x ] } ):
    repeat
        P[ idx + 1 ] := { }:
        for p in P[ idx ] do
            for y in _back_reach( p[ 1 ] ) do
                if bool( contains( p, y ) = 0 ) then
                    P[ idx + 1 ] := P[ idx + 1 ] union { [ y ].p }:
                end_if:
            end_for:
        end_for:
        idx := idx + 1:
    until bool( nops( P[ idx ] ) = 0 ) end_repeat:
    Q := { }:
    for idx from 1 to idx do
        Q := Q union { p $ p in select( P[ idx ], ( p ) -> bool( p[ 1 ] in X ) ) }:
    end_for:
end_proc:

unsafe := proc( x, P )
begin
    if bool( x in X_f ) then
        P := [ [ "unsafe( ".x." )" ].[ x." in X_f" ] ]:
        return( [ TRUE, P ] ):
    else
        return( [ FALSE, P ] ):
    end_if:
end_proc:

unreach := proc( x, P )
    local y, p, P_3, _P_3, R_3;
begin
    R_3 := TRUE:
    P_3 := [ ]:
    for p in _backward_paths( x, X_0 ) do
        _R_3 := FALSE:
        _P_3 := [ ]:
        for y in p[ 1..-2 ] do
            [ _R_3, _P_3 ] := bad( y, { }, P ):
            if bool( _R_3 ) then
                _P_3 := [ [ p ] ]._P_3:
                break:
            end_if:
        end_for:
        R_3 := R_3 and _R_3:
        P_3 := P_3._P_3:
    end_for:
    
    if bool( R_3 ) then
        P_3 := [ [ "unreach( ".x." )" ].P_3 ]:
        return( [ TRUE, P_3 ] ):
    else
        return( [ FALSE, P ] ):
    end_if:
end_proc:

bad := proc( x, Y, P )
    local y, p, P_1, P_2, P_3, _P_3, R_1, R_2, R_3, _R_3;
begin
    [ R_1, P_1 ] := unsafe( x, Y, P ):
    
    R_3 := TRUE:
    P_3 := [ ]:
    for p in _forward_paths( x, X_m ) do
        _R_3 := FALSE:
        _P_3 := [ ]:
        for y in p[ 2..-1 ] do
            [ _R_3, _P_3 ] := bad( y, Y union { x }, P ):
            if bool( _R_3 ) then
                _P_3 := [ [ p ] ]._P_3:
                break:
            end_if:
        end_for:
        R_3 := R_3 and _R_3:
        P_3 := P_3._P_3:
    end_for:
    
    R_2 := FALSE:
    P_2 := [ ]:
    for y in _unsafe_reach( x ) minus Y do
        [ R_2, P_2 ] := bad( y, Y union { x }, P ):
        if bool( R_2 ) then
            break:
        end_if:
    end_for:
    
    if bool( R_1 ) then
        P_1 := [ [ "bad( ".x." )" ].P_1 ]:
        return( [ TRUE, P_1 ] ):
    elif bool( R_2 ) then
        P_2 := [ [ "bad( ".x." )" ].P_2 ]:
        return( [ TRUE, P_2 ] ):
    elif bool( R_3 ) then
        P_3 := [ [ "blocking( ".x." )" ].P_3 ]:
        P_3 := [ [ "bad( ".x." )" ].P_3 ]:
        return( [ TRUE, P_3 ] ):
    else
        return( [ FALSE, P ] ):
    end_if:
end_proc:

gone := proc( x )
    local P, R;
begin
    [ R, P ] := unreach( x, [ ] ):
    if bool( R ) then
        return( [ "gone( ".x." )" ].P ):
    end_if:
    
    [ R, P ] := bad( x, { }, [ ] ):
    if bool( R ) then
        return( [ "gone( ".x." )" ].P ):
    else
        return( FAIL ):
    end_if:
end_proc: