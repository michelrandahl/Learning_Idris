module Shape

-- 'public export' will make both the type and its data constructors available outside this module
-- if it was just 'export', then functions outside this module would not be able to pattern match on the data constructors
export
data Shape = Triangle Double Double
           | Rectangle Double Double
           | Circle Double

export
triangle : Double -> Double -> Shape
triangle = Triangle

export
rectangle : Double -> Double -> Shape
rectangle = Rectangle

export
circle : Double -> Shape
circle = Circle

public export
data ShapeView : Shape -> Type where
  STriangle  : ShapeView (triangle x y)
  SRectangle : ShapeView (rectangle x y)
  SCircle    : ShapeView (circle x)

public export
shapeView : (shape : Shape) -> ShapeView shape
shapeView (Triangle x y) = STriangle
shapeView (Rectangle x y) = SRectangle
shapeView (Circle x) = SCircle

private
rectangle_area : Double -> Double -> Double
rectangle_area x y = x * y

export
area : Shape -> Double
area s' with (shapeView s')
  area (triangle x y)  | STriangle = 0.5 * rectangle_area x y
  area (rectangle x y) | SRectangle = rectangle_area x y
  area (circle x)      | SCircle = pi * x * x


