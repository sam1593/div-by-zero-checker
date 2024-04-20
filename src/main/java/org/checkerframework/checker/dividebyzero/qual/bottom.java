package org.checkerframework.checker.dividebyzero.qual;

import java.lang.annotation.ElementType;
import java.lang.annotation.Target;
import org.checkerframework.framework.qual.SubtypeOf; 

@SubtypeOf({zero.class, nonZero.class}) // Subtype of both Zero and NonZero
@Target({ElementType.TYPE_USE, ElementType.TYPE_PARAMETER})
public @interface bottom {
}

