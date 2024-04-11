# Prenex higher-order

This transformation is defined in the file `theories/higher_order.v`

## What does this transformation do?

This transformation is a very simple encoding of some higher-order features, in order to avoid complex encodings when they are not needed. It works only when there are higher-order functions taking concrete functions as arguments.

If there is a higher-order application `f g`, the transformation poses the definition `f_g := f g`
and folds the definition of `f_g` in order to hide the higher-order feature.

## An example