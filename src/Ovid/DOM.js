// DOM modelling in Javascript

// Event = { }; // prototype doesn't really need this

Element.prototype.appendChild = function(elt) {
  this.children.push(elt);
  elt.inDocument = this.inDocument; // incredible non-use of branching
}


// Most of 'document' is special-cased in Constraints.hs.
function() {
  var _createElement = function (tagName) {
    var elt = new Element(tagName);
    if (elt.href) {
      window.location = elt.href;
    }
    elt.children = [];
    elt.value = "".any(); // input elements have a value, but we pretend that all elements do.
    
    return elt; 
  };
  
  document.createElement = _createElement;
  
  document.getElementById = function (id) {
    if (id instanceof String) {
      var e = _createElement('unsafe');
      e.id = id;
      e.inDocument = true;
      return e;
    }
    else {
      return id;
    }
  };

  document.getElementsByTagName = function(tag) {
    var e = _createElement(tag);
    e.inDocument = true;
    return [e];
  };

  document.write = function(str) {
    var e = _createElement('docwrite');
    e.innerHTML = str;
    return;
  };

  document.addEventListener = addEventListener;

  document.body = _createElement('body');
}();

// Hack to fake HTMLCollections as Arrays.
Array.prototype.item = function(ix) { 
  return this[ix];
}
