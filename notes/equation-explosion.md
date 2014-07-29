# Equation explosion

Simple code:

    public void print(CssPrinterStyle printer) {
        super.print(printer);
        if(this.navindex != null) {
            this.navindex.print(printer);
        }

        if(this.navleft != null) {
            this.navleft.print(printer);
        }

        if(this.navup != null) {
            this.navup.print(printer);
        }

        if(this.navdown != null) {
            this.navdown.print(printer);
        }

        if(this.navright != null) {
            this.navright.print(printer);
        }

        if(this.unitsPerEmATSC != null) {
            this.unitsPerEmATSC.print(printer);
        }

        if(this.srcATSC != null) {
            this.srcATSC.print(printer);
        }

        if(this.panose1ATSC != null) {
            this.panose1ATSC.print(printer);
        }

        if(this.widthsATSC != null) {
            this.widthsATSC.print(printer);
        }

        if(this.bboxATSC != null) {
            this.bboxATSC.print(printer);
        }

        if(this.stemvATSC != null) {
            this.stemvATSC.print(printer);
        }

        if(this.stemhATSC != null) {
            this.stemhATSC.print(printer);
        }

        if(this.slopeATSC != null) {
            this.slopeATSC.print(printer);
        }

        if(this.ascentATSC != null) {
            this.ascentATSC.print(printer);
        }

        if(this.descentATSC != null) {
            this.descentATSC.print(printer);
        }

        if(this.capHeightATSC != null) {
            this.capHeightATSC.print(printer);
        }

        if(this.xHeightATSC != null) {
            this.xHeightATSC.print(printer);
        }

        if(this.baselineATSC != null) {
            this.baselineATSC.print(printer);
        }

        if(this.centerlineATSC != null) {
            this.centerlineATSC.print(printer);
        }

        if(this.mathlineATSC != null) {
            this.mathlineATSC.print(printer);
        }

        if(this.toplineATSC != null) {
            this.toplineATSC.print(printer);
        }

        if(this.definitionSrcATSC != null) {
            this.definitionSrcATSC.print(printer);
        }

        if(this.ATSCcolor != null) {
            this.ATSCcolor.print(printer);
        }

        if(this.dynamicRefresh != null) {
            this.dynamicRefresh.print(printer);
        }

        this.cssBackgroundATSC.print(printer);
        this.cssBorderATSC.print(printer);
    }

It produces a huge equation. Something like this:
    
    ConditionalNPE(Set(
        Set(o/w/c/p/a/DefinitionSrcATSC print(S)V #0, o/w/c/p/a/XHeightATSC print(S)V #0, o/w/c/p/a/CssBackgroundATSC print(S)V #0, o/w/c/p/a/CapHeightATSC print(S)V #0, o/w/c/p/a/SlopeATSC print(S)V #0, o/w/c/p/a/CenterlineATSC print(S)V #0, o/w/c/p/a/ATSCDynamicRefresh print(S)V #0, o/w/c/p/a/AscentATSC print(S)V #0, o/w/c/p/a/CssBorderATSC print(S)V #0, o/w/c/p/a/ToplineATSC print(S)V #0),
        Set(o/w/c/p/a/StemhATSC print(S)V #0, o/w/c/p/a/StemvATSC print(S)V #0, o/w/c/p/a/DescentATSC print(S)V #0, o/w/c/p/a/XHeightATSC print(S)V #0, o/w/c/p/a/CssBackgroundATSC print(S)V #0, o/w/c/p/a/SlopeATSC print(S)V #0, o/w/c/p/a/ATSCDynamicRefresh print(S)V #0, o/w/c/p/a/CssBorderATSC print(S)V #0, o/w/c/p/a/ToplineATSC print(S)V #0, o/w/c/p/a/BboxATSC print(S)V #0),
        Set(o/w/c/p/a/DefinitionSrcATSC print(S)V #0, o/w/c/p/a/DescentATSC print(S)V #0, o/w/c/p/a/XHeightATSC print(S)V #0, o/w/c/p/a/CssBackgroundATSC print(S)V #0, o/w/c/p/a/CapHeightATSC print(S)V #0, o/w/c/p/a/SlopeATSC print(S)V #0, o/w/c/p/a/CssBorderATSC print(S)V #0, o/w/c/p/a/MathlineATSC print(S)V #0, o/w/c/p/a/BboxATSC print(S)V #0),
        Set(o/w/c/p/a/DescentATSC print(S)V #0, o/w/c/p/a/XHeightATSC print(S)V #0, o/w/c/p/a/CssBackgroundATSC print(S)V #0, o/w/c/p/a/CapHeightATSC print(S)V #0, o/w/c/p/a/CenterlineATSC print(S)V #0, o/w/c/p/a/ATSCDynamicRefresh print(S)V #0, o/w/c/p/a/CssBorderATSC print(S)V #0, o/w/c/p/a/BaselineATSC print(S)V #0, o/w/c/p/a/MathlineATSC print(S)V #0, o/w/c/p/a/ToplineATSC print(S)V #0, o/w/c/p/a/BboxATSC print(S)V #0),
        Set(o/w/c/p/a/DefinitionSrcATSC print(S)V #0, o/w/c/p/a/StemhATSC print(S)V #0, o/w/c/p/a/StemvATSC print(S)V #0, o/w/c/p/a/DescentATSC print(S)V #0, o/w/c/p/a/CssBackgroundATSC print(S)V #0, o/w/c/p/a/CapHeightATSC print(S)V #0, o/w/c/p/a/CenterlineATSC print(S)V #0, o/w/c/p/a/AscentATSC print(S)V #0, o/w/c/p/a/CssBorderATSC print(S)V #0, o/w/c/p/a/MathlineATSC print(S)V #0, o/w/c/p/a/BboxATSC print(S)V #0),
        Set(o/w/c/p/a/DefinitionSrcATSC print(S)V #0, o/w/c/p/a/StemvATSC print(S)V #0, o/w/c/p/a/CssBackgroundATSC print(S)V #0, o/w/c/p/a/SlopeATSC print(S)V #0, o/w/c/p/a/CenterlineATSC print(S)V #0, o/w/c/p/a/ATSCColor print(S)V #0, o/w/c/p/a/ATSCDynamicRefresh print(S)V #0, o/w/c/p/a/CssBorderATSC print(S)V #0, o/w/c/p/a/ToplineATSC print(S)V #0),
        Set(o/w/c/p/a/StemhATSC print(S)V #0, o/w/c/p/a/DescentATSC print(S)V #0, o/w/c/p/a/CssBackgroundATSC print(S)V #0, o/w/c/p/a/CapHeightATSC print(S)V #0, o/w/c/p/a/CenterlineATSC print(S)V #0, o/w/c/p/a/AscentATSC print(S)V #0, o/w/c/p/a/CssBorderATSC print(S)V #0, o/w/c/p/a/MathlineATSC print(S)V #0, o/w/c/p/a/ToplineATSC print(S)V #0),
        Set(o/w/c/p/a/StemhATSC print(S)V #0, o/w/c/p/a/DescentATSC print(S)V #0, o/w/c/p/a/XHeightATSC print(S)V #0, o/w/c/p/a/CssBackgroundATSC print(S)V #0, o/w/c/p/a/ATSCColor print(S)V #0, o/w/c/p/a/CssBorderATSC print(S)V #0, o/w/c/p/a/BaselineATSC print(S)V #0, o/w/c/p/a/MathlineATSC print(S)V #0, o/w/c/p/a/ToplineATSC print(S)V #0, o/w/c/p/a/BboxATSC print(S)V #0),
        Set(o/w/c/p/a/StemhATSC print(S)V #0, o/w/c/p/a/StemvATSC print(S)V #0, o/w/c/p/a/XHeightATSC print(S)V #0, o/w/c/p/a/CssBackgroundATSC print(S)V #0, o/w/c/p/a/CapHeightATSC print(S)V #0, o/w/c/p/a/SlopeATSC print(S)V #0, o/w/c/p/a/ATSCDynamicRefresh print(S)V #0, o/w/c/p/a/CssBorderATSC print(S)V #0),
        Set(o/w/c/p/a/DefinitionSrcATSC print(S)V #0, o/w/c/p/a/DescentATSC print(S)V #0, o/w/c/p/a/XHeightATSC print(S)V #0, o/w/c/p/a/CssBackgroundATSC print(S)V #0, o/w/c/p/a/SlopeATSC print(S)V #0, o/w/c/p/a/CenterlineATSC print(S)V #0, o/w/c/p/a/ATSCColor print(S)V #0, o/w/c/p/a/ATSCDynamicRefresh print(S)V #0, o/w/c/p/a/AscentATSC print(S)V #0, o/w/c/p/a/CssBorderATSC print(S)V #0),
        Set(o/w/c/p/a/DefinitionSrcATSC print(S)V #0, o/w/c/p/a/StemhATSC print(S)V #0, o/w/c/p/a/DescentATSC print(S)V #0, o/w/c/p/a/XHeightATSC print(S)V #0, o/w/c/p/a/CssBackgroundATSC print(S)V #0, o/w/c/p/a/ATSCColor print(S)V #0, o/w/c/p/a/ATSCDynamicRefresh print(S)V #0, o/w/c/p/a/AscentATSC print(S)V #0, o/w/c/p/a/CssBorderATSC print(S)V #0, o/w/c/p/a/ToplineATSC print(S)V #0, o/w/c/p/a/BboxATSC print(S)V #0),
        Set(o/w/c/p/a/DefinitionSrcATSC print(S)V #0, o/w/c/p/a/StemhATSC print(S)V #0, o/w/c/p/a/CssBackgroundATSC print(S)V #0, o/w/c/p/a/ATSCColor print(S)V #0, o/w/c/p/a/ATSCDynamicRefresh print(S)V #0, o/w/c/p/a/CssBorderATSC print(S)V #0, o/w/c/p/a/BaselineATSC print(S)V #0, o/w/c/p/a/BboxATSC print(S)V #0),
        Set(o/w/c/p/a/StemhATSC print(S)V #0, o/w/c/p/a/DescentATSC print(S)V #0, o/w/c/p/a/CssBackgroundATSC print(S)V #0, o/w/c/p/a/CapHeightATSC print(S)V #0, o/w/c/p/a/CenterlineATSC print(S)V #0, o/w/c/p/a/ATSCColor print(S)V #0, o/w/c/p/a/ATSCDynamicRefresh print(S)V #0, o/w/c/p/a/CssBorderATSC print(S)V #0, o/w/c/p/a/BaselineATSC print(S)V #0, o/w/c/p/a/MathlineATSC print(S)V #0),
        Set(o/w/c/p/a/StemhATSC print(S)V #0, o/w/c/p/a/StemvATSC print(S)V #0, o/w/c/p/a/DescentATSC print(S)V #0, o/w/c/p/a/XHeightATSC print(S)V #0, o/w/c/p/a/CssBackgroundATSC print(S)V #0, o/w/c/p/a/CapHeightATSC print(S)V #0, o/w/c/p/a/SlopeATSC print(S)V #0, o/w/c/p/a/AscentATSC print(S)V #0, o/w/c/p/a/CssBorderATSC print(S)V #0, o/w/c/p/a/MathlineATSC print(S)V #0),
        Set(o/w/c/p/a/DefinitionSrcATSC print(S)V #0, o/w/c/p/a/StemhATSC print(S)V #0, o/w/c/p/a/StemvATSC print(S)V #0, o/w/c/p/a/CssBackgroundATSC print(S)V #0, o/w/c/p/a/CapHeightATSC print(S)V #0, o/w/c/p/a/CenterlineATSC print(S)V #0, o/w/c/p/a/CssBorderATSC print(S)V #0, o/w/c/p/a/BaselineATSC print(S)V #0, o/w/c/p/a/ToplineATSC print(S)V #0, o/w/c/p/a/BboxATSC print(S)V #0),
        Set(o/w/c/p/a/StemhATSC print(S)V #0, o/w/c/p/a/StemvATSC print(S)V #0, o/w/c/p/a/DescentATSC print(S)V #0, o/w/c/p/a/XHeightATSC print(S)V #0, o/w/c/p/a/CssBackgroundATSC print(S)V #0, o/w/c/p/a/SlopeATSC print(S)V #0, o/w/c/p/a/CssBorderATSC print(S)V #0, o/w/c/p/a/BaselineATSC print(S)V #0, o/w/c/p/a/BboxATSC print(S)V #0),
        Set(o/w/c/p/a/StemhATSC print(S)V #0, o/w/c/p/a/StemvATSC print(S)V #0, o/w/c/p/a/DescentATSC print(S)V #0, o/w/c/p/a/CssBackgroundATSC print(S)V #0, o/w/c/p/a/SlopeATSC print(S)V #0, o/w/c/p/a/AscentATSC print(S)V #0, o/w/c/p/a/CssBorderATSC print(S)V #0, o/w/c/p/a/MathlineATSC print(S)V #0),
        Set(o/w/c/p/a/StemvATSC print(S)V #0, o/w/c/p/a/DescentATSC print(S)V #0, o/w/c/p/a/CssBackgroundATSC print(S)V #0, o/w/c/p/a/CapHeightATSC print(S)V #0, o/w/c/p/a/SlopeATSC print(S)V #0, o/w/c/p/a/CenterlineATSC print(S)V #0, o/w/c/p/a/ATSCColor print(S)V #0, o/w/c/p/a/ATSCDynamicRefresh print(S)V #0, o/w/c/p/a/AscentATSC print(S)V #0, o/w/c/p/a/CssBorderATSC print(S)V #0, o/w/c/p/a/BaselineATSC print(S)V #0, o/w/c/p/a/MathlineATSC print(S)V #0, o/w/c/p/a/ToplineATSC print(S)V #0, o/w/c/p/a/BboxATSC print(S)V #0),
        Set(o/w/c/p/a/DefinitionSrcATSC print(S)V #0, o/w/c/p/a/CssBackgroundATSC print(S)V #0, o/w/c/p/a/CapHeightATSC print(S)V #0, o/w/c/p/a/SlopeATSC print(S)V #0, o/w/c/p/a/CenterlineATSC print(S)V #0, o/w/c/p/a/ATSCColor print(S)V #0, o/w/c/p/a/CssBorderATSC print(S)V #0, o/w/c/p/a/MathlineATSC print(S)V #0),
        Set(o/w/c/p/a/StemhATSC print(S)V #0, o/w/c/p/a/XHeightATSC print(S)V #0, o/w/c/p/a/CssBackgroundATSC print(S)V #0, o/w/c/p/a/CapHeightATSC print(S)V #0, o/w/c/p/a/SlopeATSC print(S)V #0, o/w/c/p/a/CssBorderATSC print(S)V #0, o/w/c/p/a/BaselineATSC print(S)V #0, o/w/c/p/a/MathlineATSC print(S)V #0),
        Set(o/w/c/p/a/StemhATSC print(S)V #0, o/w/c/p/a/CssBackgroundATSC print(S)V #0, o/w/c/p/a/SlopeATSC print(S)V #0, o/w/c/p/a/CssBorderATSC print(S)V #0, o/w/c/p/a/ToplineATSC print(S)V #0),
        Set(o/w/c/p/a/DefinitionSrcATSC print(S)V #0, o/w/c/p/a/StemhATSC print(S)V #0, o/w/c/p/a/DescentATSC print(S)V #0, o/w/c/p/a/CssBackgroundATSC print(S)V #0, o/w/c/p/a/SlopeATSC print(S)V #0, o/w/c/p/a/CenterlineATSC print(S)V #0, o/w/c/p/a/ATSCDynamicRefresh print(S)V #0, o/w/c/p/a/AscentATSC print(S)V #0, o/w/c/p/a/CssBorderATSC print(S)V #0),
        Set(o/w/c/p/a/DefinitionSrcATSC print(S)V #0, o/w/c/p/a/DescentATSC print(S)V #0, o/w/c/p/a/CssBackgroundATSC print(S)V #0, o/w/c/p/a/SlopeATSC print(S)V #0, o/w/c/p/a/AscentATSC print(S)V #0, o/w/c/p/a/CssBorderATSC print(S)V #0, o/w/c/p/a/BaselineATSC print(S)V #0, o/w/c/p/a/BboxATSC print(S)V #0),
        Set(o/w/c/p/a/DefinitionSrcATSC print(S)V #0, o/w/c/p/a/StemvATSC print(S)V #0, o/w/c/p/a/DescentATSC print(S)V #0, o/w/c/p/a/XHeightATSC print(S)V #0, o/w/c/p/a/CssBackgroundATSC print(S)V #0, o/w/c/p/a/SlopeATSC print(S)V #0, o/w/c/p/a/ATSCColor print(S)V #0, o/w/c/p/a/ATSCDynamicRefresh print(S)V #0, o/w/c/p/a/AscentATSC print(L

The reason is that in this specific case DNF is not optimal at all.
