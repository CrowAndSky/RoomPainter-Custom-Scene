
'use strict';

// ---------==|  Array global vars  |==---------
var edgeNodes = [], // convolution detected edges - created at initialization and stays constant
canRender = [], // JS object with diffmap and tinting methods
colorSpaces = []; // 2-D map of plaette colors

// ---------==|  Canvas object global vars  |==---------
var canWorking, // used to with flood fillmask generation
ctxWorking, // context reused when performing flood fills
canRender, // Where we render tinted surfaces
ctxRender,
//ctxEdgeMap, // holds convolution map of room image

// ---------==|  Pixel data global vars  |==---------
tintedPixels = [], // TO DO - REPLACE THIS IN FLOOD FILL WITH PIXTEMP
pixRef, // initial (reference) room image pixels
pixTemp, // utility - hold pixle data before passing to context
pixRender,
pixRenderData,
pixRenderBuffer,
renderObject,

// ---------==|  UI element global vars  |==---------
theSwatches, // UI sawtch elements
imgTemp, //utility - pass image into Canvas method or function

// ---------==|  UI state global vars  |==---------
canvasX, // X position of interface canvas(es)
canvasY, // Y position of interface canvas(es)
canvasW, // width of interface canvas(es)
canvasH, // height of interface canvas(es)
currentY, // last cursor position - used between events and methods
currentX, // last cursor position - used between events and methods
newY, // cursor position during click events
newX, // cursor position during click events
UImode, // current interaction state
globalTemp,
currentColor, // NOT SURE I NEED: used in render object
renderColor = [],
valueDiff; // NOT SURE I NEED: used in render object

// ---------==|  Device-specific global vars  |==---------
var deviceTouch = false;
var loadingApp = true;
var displayLoading = true;
var Int32support = false;

// ---------==|  Namespaces  |==---------
var Utility = {};
var Maps = {};
var Filters = {};
var Tools = {};
var Tint = {};

Utility.modeArray = function (array) {
	if(array.length == 0)
		return null;
	var modeMap = {};
	var maxCount = 1, modes = [array[0]];
	for(var i = 0; i < array.length; i++)
	{
		var el = array[i];
		if(modeMap[el] == null)
			modeMap[el] = 1;
		else
			modeMap[el]++;  
		if(modeMap[el] > maxCount)
		{
			modes = [el];
			maxCount = modeMap[el];
		}
		else if(modeMap[el] == maxCount)
		{
			modes.push(el);
			maxCount = modeMap[el];
		}
	}
	return modes;
}

Utility.setRenderColor = function (colorCurrent) {
	var matchColors = /rgb\((\d{1,3}), (\d{1,3}), (\d{1,3})\)/;
	var match = matchColors.exec(colorCurrent);
	renderColor[0] =  parseInt(match[1]);
	renderColor[1] =  parseInt(match[2]);
	renderColor[2] =  parseInt(match[3]);
}

Utility.linePoints = function (x1, y1, x2, y2)
{
    var dx = x2 - x1; var sx = 1;
    var dy = y2 - y1; var sy = 1;
    if (dx < 0)    {
        sx = -1;
        dx = -dx;
    }
    if (dy < 0)    {
        sy = -1;
        dy = -dy;
    }
    dx = dx << 1;
    dy = dy << 1;
    // At this point x1 y1 is the initial line point, which we already have
    if (dy < dx)
    {    
        var fraction = dy - (dx>>1);
        while (x1 != x2)
        {
            if (fraction >= 0)
            {
                y1 += sy;
                fraction -= dx;
            }
            fraction += dy;
            x1 += sx;
            // This is a point along our line, add it to edge nodes
            edgeNodes[x1][y1] = true;
        }
    } 
    else 
    {
        var fraction = dx - (dy>>1);        
        while (y1 != y2)
        {
            if (fraction >= 0)
            {
                x1 += sx;
                fraction -= dy;
            }
            fraction += dx;
            y1 += sy;
            // This is a point along our line, add it to edge nodes
            edgeNodes[x1][y1] = true;
        }    
    }
}

Filters.tmpCanvas = document.createElement('canvas');
Filters.tmpCtx = Filters.tmpCanvas.getContext('2d');

Filters.createImageData = function(w,h) {
  return this.tmpCtx.createImageData(w,h);
};

Filters.grayscale = function(pixels, args) {
  var d = pixels.data;
  for (var i=0; i<d.length; i+=4) {
	var r = d[i];
	var g = d[i+1];
	var b = d[i+2];
	// CIE luminance, for reference only: var v = 0.2126*r + 0.7152*g + 0.0722*b;
	var v = (r + g + b)/3;
	d[i] = d[i+1] = d[i+2] = v
  }
  return pixels;
};

Filters.convoluteFloat32 = function(pixels, weights, opaque) {
  var side = Math.round(Math.sqrt(weights.length));
  var halfSide = Math.floor(side/2);

  var src = pixels.data;
  var sw = pixels.width;
  var sh = pixels.height;

  var w = sw;
  var h = sh;
  var output = {
	width: w, height: h, data: new Float32Array(w*h*4)
  };
  var dst = output.data;

  var alphaFac = opaque ? 1 : 0;

  for (var y=0; y<h; y++) {
	for (var x=0; x<w; x++) {
	  var sy = y;
	  var sx = x;
	  var dstOff = (y*w+x)*4;
	  var r=0, g=0, b=0, a=0;
	  for (var cy=0; cy<side; cy++) {
		for (var cx=0; cx<side; cx++) {
		  var scy = Math.min(sh-1, Math.max(0, sy + cy - halfSide));
		  var scx = Math.min(sw-1, Math.max(0, sx + cx - halfSide));
		  var srcOff = (scy*sw+scx)*4;
		  var wt = weights[cy*side+cx];
		  r += src[srcOff] * wt;
		  g += src[srcOff+1] * wt;
		  b += src[srcOff+2] * wt;
		  a += src[srcOff+3] * wt;
		}
	  }
	  dst[dstOff] = r;
	  dst[dstOff+1] = g;
	  dst[dstOff+2] = b;
	  dst[dstOff+3] = a + alphaFac*(255-a);
	}
  }
  return output;
};

Maps.initEdge = function() {
  var px = Filters.grayscale(pixTemp);

  var vertical = Filters.convoluteFloat32(px,
	[-1,-2,-1,
	  0, 0, 0,
	  1, 2, 1]);
  var horizontal = Filters.convoluteFloat32(px,
	[-1,0,1,
	 -2,0,2,
	 -1,0,1]);
  tintedPixels = Filters.createImageData(vertical.width, vertical.height);

  var pixelComponentWidth = vertical.width * 4;

  for (var i=0; i<vertical.width; i++) {
	edgeNodes[i] = [];

	for (var j=0; j<vertical.height; j++) {
	  edgeNodes[i][j] = false;
	}
  }

  for (var i=0; i<tintedPixels.data.length; i+=4) {
	var v = Math.abs(vertical.data[i]);
	var h = Math.abs(horizontal.data[i]);

	if (v + h >100) {
	  if (i===0) {
		var currentY = 0;
	  } else {
		var currentY = Math.floor(i/pixelComponentWidth);
	  }
	  var currentX = Math.floor((i - currentY * pixelComponentWidth)/4);
	  edgeNodes[currentX][currentY] = true;

	  tintedPixels.data[i] = 0;
	tintedPixels.data[i+1] = 255;
	tintedPixels.data[i+2] = 0;
	tintedPixels.data[i+3] = 255;
	} else {
		tintedPixels.data[i+3] = 0;
	}

  }
  ctxWorking.putImageData(tintedPixels, 0, 0);
}

Tools.floodFill = function() {
	var dx = [ 0, -1, +1,  0];
	var dy = [-1,  0,  0, +1];
	var stack = [];
	stack.push(currentX);
	stack.push(currentY);

	while (stack.length > 0) {
		var curPointY = stack.pop();
		var curPointX = stack.pop();

		for (var i = 0; i < 4; i++) {
			var nextPointX = curPointX + dx[i];
			var nextPointY = curPointY + dy[i];

			if (nextPointX < 0 || nextPointY < 0 || nextPointX >= canvasW || nextPointY >= canvasH) {
				continue;
			}

			var nextPointOffset = (nextPointY * canvasW + nextPointX);

			if (edgeNodes[nextPointX][nextPointY] == false) {

				var currentIndex = (nextPointY * canvasW + nextPointX) * 4;

				edgeNodes[nextPointX][nextPointY] = true;

				tintedPixels.data[currentIndex] = 0;
				tintedPixels.data[currentIndex+1] = 0;
				tintedPixels.data[currentIndex+2] = 255;

				renderObject.maskedPixels.push(currentIndex);
				renderObject.maskedPixels.push(pixRef.data[currentIndex]);
				renderObject.maskedPixels.push(pixRef.data[currentIndex+1]);
				renderObject.maskedPixels.push(pixRef.data[currentIndex+2]);
				renderObject.maskedPixels.push(pixRef.data[currentIndex+3]);

				stack.push(nextPointX);
				stack.push(nextPointY);
			}
		}
	}

	// I don't think I need this
	ctxWorking.putImageData(tintedPixels, 0, 0);
}

Tint.RenderCanvasObject = function () {

	/*################# DATA DICTIONARY #################
    this.imageData : original canvas image data
    this.pixelData : original canvas image pixel array
    pixLength : original canvas image pixel array length
    this.colorsSorted : grayscale value of all non-transparent pixels
    this.renderMap : a 256 node object array (representing each possible pixel color component value). This is the lookup table of the value adjusted
        color for each applied tint. We calculate these values once for each of 256 possible relative original grayscale values of every image
        pixel and store them here to be referenced by value as the imageData is updated. Regardless of whether the browser supports Int32,
        each object has the following property:
        valueDiff: the difference between the node's index and the average value of all non-transparent pixels in the image.
        If the browser supports Int32 there is just one additional property for each object, which holds all four pixel components in a single value:
        currentColor: This is recalculated each time a different tint is applied
        If the browser doesn't support Int32 there are three additional property for each object: "rVal", "gVal", and "bVal" -
        one property for each of the pixel primary hue components.
    this.renderedPixels : heart of the tinting operation, an object for each non-transparent pixel. it has two properties:
        hue: the grayscale value of the current pixel, this will be used as an index to compare against the tint lookup array
        index: the array index of all original pixels, used to write the updated tint values to the appropriate canvas imageData values

    ##################################*/

	var that = this;
	this.valueData = {};
	this.colorsAll = [];
	this.colorsSorted = [];
	this.alphaCorrections = [];
	this.renderMap = [];
	this.renderedPixels = [];
	this.averageValue;
	this.maskedPixels = []; // Pixels captured by the current mask
	
	this.makeDiffMap = function(){
		var i = 0; //index in the array of all pixels
		var k = 0; //index in the array of all non-transparent pixels
		var pixLength = this.maskedPixels.length;

		for (i = 0; i < pixLength; i += 5) { // iterating by 5 for each of the pixel channels plus masterPixelIndex value
				globalTemp = (this.maskedPixels[i+1] + this.maskedPixels[i+2] + this.maskedPixels[i+3]) / 3;
				this.colorsSorted[k] = globalTemp; //building the array of values to find averege from
				this.renderedPixels[k] = {hue : globalTemp,  //this will be the index of the tinted color lookup array
										index: this.maskedPixels[i]};  //index in the 32 bit array of all canvas pixels
				k++;
		}

		this.averageValue = Utility.modeArray(this.colorsSorted);

		for (var i = 0; i < 256; i++) {
			/* For each value step between black and white, determine the difference between that and the mode value for the render pixel range.
			We'll then apply this difference to in the renderMap created in the tintSurface method. */
			this.renderMap[i] = {valueDiff : i - this.averageValue};
		}
	}

	this.tintSurface = function (){

		var rChannel, bChannel, gChannel;

		if (Int32support) {
			/* First we update the renderMap map by tinting each node to the currently selected palette color.
				We combine each of the pixel primary hue components into a single Int32 value using a bitwise shift left.
				Note that we assume full opacity (255) for the alpha component, which will mean update those values later for some pixels.*/
			for (var i = 0; i < 256; i++) {
				rChannel = Math.min(251, Math.max(0, renderColor[0] + this.renderMap[i].valueDiff));
				gChannel = Math.min(251, Math.max(0, renderColor[1] + this.renderMap[i].valueDiff));
				bChannel = Math.min(251, Math.max(0, renderColor[2] + this.renderMap[i].valueDiff));
				this.renderMap[i].currentColor = (255   << 24) |    // alpha
					(bChannel << 16) |    // blue
					(gChannel <<  8) |    // green
					rChannel;
			}

			/* Second we update all renderedPixels using the "index" property of the object as the lookup index in the renderMap object */
			var rendPixLength = this.renderedPixels.length;			
			for (var i = 0; i < rendPixLength; i++) {
				/* PROBLEM: pixRenderBuffer[this.renderedPixels[i].index] is undefined at this point (but is renderedPixels[i].index]?)
				if (i<100) {
					console.log("i: " + i + "      pixRenderBuffer[this.renderedPixels[i].index]: " + pixRenderBuffer[this.renderedPixels[i].index] + "      this.renderMap[this.renderedPixels[i].hue].currentColor:" + this.renderMap[this.renderedPixels[i].hue].currentColor);
				}
				*/

				pixRenderBuffer[this.renderedPixels[i].index] = this.renderMap[this.renderedPixels[i].hue].currentColor;
			}

			console.log("1");

		} else {
			console.log("bad");
			/*  First we update the renderMap map by tinting each node to the currently selected palette color.
			We write each of the updated pixel primary hue components a separate property of the current renderMap object. */
			var i = 0;

			for (var i = 0; i < 256; i++) {
				this.renderMap[i].rVal = Math.min(251, Math.max(0, renderColor[0] + this.renderMap[i].valueDiff));
				this.renderMap[i].gVal = Math.min(251, Math.max(0, renderColor[1] + this.renderMap[i].valueDiff));
				this.renderMap[i].bVal = Math.min(251, Math.max(0, renderColor[2] + this.renderMap[i].valueDiff));
			}

			// Second we update all renderedPixels using the "index" property of the object as the lookup index in the renderMap object
			var rendPixLength = this.renderedPixels.length;

			for (var i = 0; i < rendPixLength; i++) {
				pixRenderData[this.renderedPixels[i].index   ] = this.renderMap[this.renderedPixels[i].hue].rVal;
				pixRenderData[this.renderedPixels[i].index +1] = this.renderMap[this.renderedPixels[i].hue].gVal;
				pixRenderData[this.renderedPixels[i].index +2] = this.renderMap[this.renderedPixels[i].hue].bVal;
			}
		}

		ctxRender.putImageData(pixRender, 0, 0);

		console.log("2");
	}
}

function initApp() {

	/*------=| wwwwwwwwwww |=------*/

	/* ------=| Set device/browser specific vars |=------ */
	if (Modernizr.touch){
		$('body').addClass('touchEnabled');
		deviceTouch = true;
	};

	// if(typeof Int32Array !== 'undefined'){
	// 	//Int32support = true;
	// 	console.log("your browser supports Int32 Arrays!");
	// } else {
	// 	console.log("your browser does NOT support Int32 Arrays");
	// }

	/*------=| Init DOM dependant global vars |=------*/
	imgTemp = $('#imgRoom');
	canvasW = imgTemp.width();
	canvasH = imgTemp.height();
	theSwatches = $('#swatches');

	canWorking = $('#can-working');
	canWorking.get(0).width = canvasW;
	canWorking.get(0).height = canvasH;
	ctxWorking = canWorking.get(0).getContext('2d');

	canvasX = canWorking.offset().left;
	canvasY = canWorking.offset().top;
	
	canRender = $('#can-render');
	canRender.get(0).width = canvasW;
	canRender.get(0).height = canvasH;
	ctxRender = canRender.get(0).getContext('2d');

	/*------=| Init working contexts and create edge map |=------*/
	ctxWorking.drawImage(imgTemp.get(0), 0, 0);
	ctxRender.drawImage(imgTemp.get(0), 0, 0);

	// Set reference and temp pixel data arrays to the source image. We'll use the temp pixel array to init edge nodes in the next statement
	pixRef = pixTemp = ctxWorking.getImageData(0, 0, canvasW, canvasH);
	pixRender = ctxRender.getImageData(0, 0, canvasW, canvasH);
	pixRenderData = pixRender.data;

	if (Int32support) {
		console.log("set buff");
		pixRenderBuffer = new Int32Array(pixRender.data.buffer);
	}

	Maps.initEdge();

	//this is just while testing:
	// UImode = "mark-edge-start";

	/*------=| Create rendering object |=------*/
	renderObject = new Tint.RenderCanvasObject();

	/*------=| Attach UI events |=------*/

	$("#masking-UI").on("click", "#ctrl-mark-erase", function() {
		UImode = "mark-erase-start";
	});
	
	$("#masking-UI").on("click", "#ctrl-mark-line", function() {
		UImode = "mark-line-start";
	});

	$("#masking-UI").on("click", "#ctrl-mark-free", function() {
		UImode = "mark-free-start";
	});

	$("#masking-UI").on("click", "#ctrl-mark-int", function() {
		UImode = "mark-interior";
	});

	$("#masking-UI").on("click", "#ctrl-mask-done", function() {
		UImode = "mark-finish";
		$('body').removeClass('mode-mask');
		imgTemp.css('visibility','hidden')
		renderObject.makeDiffMap();
		// renderObject.tintSurface();
	});

	$("#canvasWrapper").on("click", "#can-working", function(e) {
		switch (UImode) {
			case "mark-interior":
				currentX = parseInt(e.pageX - canvasX);
				currentY = parseInt(e.pageY - canvasY);
				Tools.floodFill();
				break;

			case "mark-line-start":
				currentX = parseInt(e.pageX - canvasX);
				currentY = parseInt(e.pageY - canvasY);
				currentX = currentX < 8 || currentX > (canvasW - 8) ? 0 : currentX;
				currentY = currentY < 8 || currentY > (canvasH - 8) ? 0 : currentY;
				ctxWorking.strokeStyle = '#00ff00';
				ctxWorking.moveTo(currentX,currentY);
				ctxWorking.beginPath();
				UImode = "mark-line";
				break;

			case "mark-line":
				ctxWorking.lineTo(currentX,currentY);
				ctxWorking.stroke();
				newX = parseInt(e.pageX - canvasX);
				newY = parseInt(e.pageY - canvasY);
				newX = newX < 8 || newX > (canvasW - 8) ? 0 : newX;
				newY = newY < 8 || newY > (canvasH - 8) ? 0 : newY;
				var newPoints = Utility.linePoints(currentX, currentY, newX, newY);
				currentY = newY;
				currentX = newX;
				// TO-DO WHY do I have to do this twice?
				ctxWorking.lineTo(currentX,currentY);
				ctxWorking.stroke();
				break;

		}
	});

	$("#canvasWrapper").on("dblclick", "#can-working", function(e) {
		if (UImode === "mark-edge" || UImode === "mark-free") {
			UImode = "default";
			tintedPixels = ctxWorking.getImageData(0, 0, canvasW, canvasH);
		}
	});

	$("#canvasWrapper").on("mousedown", "#can-working", function(e) {
		
		if (UImode === "mark-free-start") {
			currentX = parseInt(e.pageX - canvasX);
			currentY = parseInt(e.pageY - canvasY);
			ctxWorking.moveTo(currentX,currentY);
			ctxWorking.strokeStyle = '#00ff00';
			ctxWorking.beginPath();
			UImode = "mark-free"
		} else if (UImode === "mark-erase-start") {
			currentX = parseInt(e.pageX - canvasX);
			currentY = parseInt(e.pageY - canvasY);
			UImode = "mark-erase";
		}

	});

	$("#canvasWrapper").on("mousemove", "#can-working", function(e) {
		newX = parseInt(e.pageX - canvasX);
		newY = parseInt(e.pageY - canvasY);

		if (UImode === "mark-free") {
			var newPoints = Utility.linePoints(currentX, currentY, newX, newY);
			currentY = newY;
			currentX = newX;
			ctxWorking.lineTo(currentX,currentY);
      		ctxWorking.stroke();
      		console.log("mark freehand at ====== X: " + currentX + "      Y: " + currentY );
		} else if (UImode === "mark-erase") {
			var dx = [0,  0, +1,  0,  0, -1, -1,  0,  0,  0, +1, +1, +1,  0,  0,  0,  0, -1, -1, -1, -1,  0,  0,  0,  0];
			var dy = [0, -1,  0, +1, +1,  0,  0, -1, -1, -1,  0,  0,  0, +1, +1, +1, +1,  0,  0,  0,  0, -1, -1, -1, -1];
			// console.log("mark erase at ====== X: " + newX + "      Y: " + newY );
			var currentIndex = (newY * canvasW + newX) * 4;
			for (var i = 0; i < 25; i++) {
				newX = newX + dx[i];
				newY = newY + dy[i];
				currentIndex = (newY * canvasW + newX) * 4;
				tintedPixels.data[currentIndex+3] = 0;
				edgeNodes[newX][newY] = false;
			}
		}
	});

	$("#canvasWrapper").on("mouseup", "#can-working", function(e) {
		if (UImode === "mark-free") {
			UImode = "default";
		} else if (UImode === "mark-erase") {
			UImode = "default";
			ctxWorking.putImageData(tintedPixels, 0, 0);
			console.log("erase");
		}
	});

	$('#swatches').on('click', 'img', function(event) {
        currentColor = $(this).parent().css('backgroundColor');
        Utility.setRenderColor(currentColor);
        renderObject.tintSurface();
        console.log(currentColor);
    });



	for (var x = 0; x < 8; x++) {
		colorSpaces[x] = [];
		for (var y = 0; y < 10; y++) {
			var currentColor = theSwatches.find('div').eq(x * 10 + y).css('backgroundColor');
			var matchColors = /rgb\((\d{1,3}), (\d{1,3}), (\d{1,3})\)/;
			var match = matchColors.exec(currentColor);
			colorSpaces[x][y] = {r:parseInt(match[1]),g:parseInt(match[2]),b:parseInt(match[3])};
		}
	}


	// $( "#wwwwww" ).on( "click", "trwwwwwww", function() {
	// 	wwwwwwww
	// });

	

} // end initApp